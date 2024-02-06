//! Contains logic for displaying a computed [Layout] in a pretty format
//! that can be queried by users.
//!
//! @@Improvements:
//!
//! 1. Since the layout printer is only a shallow printer, an improvement could
//! be made to print the layout of the types that are nested within the type,
//! and possibly exploring the nested structure:
//! ```notrust
//! struct Item (
//!    item: ( #layout_of (y: i32, x: i32), z: [i32; 3]
//!     ...
//! )
//! ```
//!
//!
//! 2. Add unit tests for some layout printing

use std::{fmt, iter};

use hash_source::identifier::Identifier;
use hash_storage::store::statics::StoreId;
use hash_target::{
    abi::AbiRepresentation, data_layout::HasDataLayout, primitives::IntTy, size::Size,
};
use hash_utils::{index_vec::index_vec, tree_writing::CharacterSet};

use crate::{
    compute::LayoutComputer,
    ty::{ReprTy, VariantIdx},
    FieldLayout, Layout, LayoutId, LayoutShape, TyInfo, Variants,
};

/// [LayoutWriterConfig] stores all of the configuration for the [LayoutWriter]
/// uses, it includes the character set that it should use for the layout.
pub struct LayoutWriterConfig {
    /// The character to use for the top left corner of a box, e.g. `┌` or `+`.
    pub top_left: char,

    /// The character to use for the top right corner of a box, e.g. `┐` or `+`.
    pub top_right: char,

    /// The character to use for the bottom left corner of a box, e.g. `└` or
    /// `+`.
    pub bottom_left: char,

    /// The character to use for the bottom right corner of a box, e.g. `┘` or
    /// `+`.
    pub bottom_right: char,

    /// The character to use for the top center of a box, e.g. `┬` or `+`.
    pub center_top: char,

    /// The character to use for the bottom center of a box, e.g. `┴` or `+`.
    pub center_bottom: char,

    /// The character to use for the left center of a box, e.g. `├` or `+`.
    pub center_left: char,

    /// The character to use for the right center of a box, e.g. `┤` or `+`.
    pub center_right: char,

    /// The character to use for the center of a box, e.g. `┼` or `+`.
    pub center: char,

    /// The vertical bar connecting character to use, e.g. `│` or `|`.
    pub vertical: char,

    /// The horizontal bar connecting character to use, e.g. `─` or `-`.
    pub horizontal: char,
}

impl LayoutWriterConfig {
    /// Create a [LayoutWriterConfig] based on the [CharacterSet].
    pub fn from_character_set(set: CharacterSet) -> Self {
        match set {
            CharacterSet::Unicode => Self::unicode(),
            CharacterSet::Ascii => Self::ascii(),
        }
    }

    /// Returns a [LayoutWriterConfig] that uses unicode box drawing
    /// characters.
    pub fn unicode() -> Self {
        Self {
            top_left: '┌',
            top_right: '┐',
            bottom_left: '└',
            bottom_right: '┘',
            center_top: '┬',
            center_bottom: '┴',
            center_left: '├',
            center_right: '┤',
            center: '┼',
            vertical: '│',
            horizontal: '─',
        }
    }

    /// Create a new [LayoutWriterConfig] that uses ASCII characters.
    pub fn ascii() -> Self {
        Self {
            top_left: '+',
            top_right: '+',
            bottom_left: '+',
            bottom_right: '+',
            center_top: '+',
            center_bottom: '+',
            center_left: '+',
            center_right: '+',
            center: '+',
            vertical: '|',
            horizontal: '-',
        }
    }

    /// Get the relevant character for the given position in the box,
    /// and the given maximum position. The coordinate system assumes that
    /// the top left corner is `(0, 0)`, and the bottom right corner is `(max.0,
    /// max.1)`.
    fn connector(&self, pos: (usize, usize), max: (usize, usize)) -> char {
        match pos {
            (0, 0) => self.top_left,
            (0, x) if x == max.1 => self.top_right,
            (x, 0) if x == max.0 => self.bottom_left,
            (x, y) if x == max.0 && y == max.1 => self.bottom_right,
            (0, _) => self.center_top,
            (x, _) if x == max.0 => self.center_bottom,
            (_, 0) => self.center_left,
            (_, y) if y == max.1 => self.center_right,
            _ => self.center,
        }
    }
}

/// The content of the [Layout] drawing box produced by the
/// [LayoutWriter].
#[derive(Debug, Clone)]
pub enum BoxContent {
    Content {
        /// The title of the box.
        title: Option<String>,

        /// The content of the box. Every newline in the box will create
        /// a hard break in the content box which would mean that the lines
        /// are all aligned on the left.
        content: String,
    },

    /// A box that represents a padding between two fields.
    Pad { size: Size },

    /// A box that represents an empty space.
    Empty { width: usize },
}

impl BoxContent {
    /// Create a new [BoxContent] with the given title and content.
    pub fn new(title: String, content: String) -> Self {
        Self::Content { title: Some(title), content }
    }

    /// Create a new [BoxContent] with the given content and without
    /// a title.
    pub fn new_content(content: String) -> Self {
        Self::Content { title: None, content }
    }

    /// Create a new [BoxContent] that represents a padding between two
    /// fields.
    pub fn new_pad(size: Size) -> Self {
        Self::Pad { size }
    }

    /// Create a new [BoxContent] that represents an empty space.
    pub fn new_empty(width: usize) -> Self {
        Self::Empty { width }
    }

    /// Compute the number of lines that this [BoxContent] will take up.
    ///
    /// N.B. One line takes up for the title, spacing between title and
    /// content, and then the number of lines in the content.
    ///
    /// # Example
    ///
    /// ```ignore
    /// +-----------------+
    /// | foo: u32        |
    /// |                 |
    /// | size = 2        |
    /// | offset = 0      |
    /// +-----------------+
    /// ```
    ///
    /// Calling [`BoxContent::height`] on the above box will return
    /// `4`.
    ///
    /// N.B. Additionally, calling [`BoxContent::height`] on a box
    /// that is [`BoxContent::Pad`] is not valid since the box is not
    /// sized, as it's size is dependant on all other box sizes. The
    /// minimum size of a [`BoxContent::Pad`] is `1`. For example:
    /// ```ignore
    /// +-------------+
    /// | 1byte (pad) |
    /// +-------------+
    /// ```
    pub fn height(&self) -> usize {
        if let Self::Content { title, content } = self {
            // If there are no lines, then don't use any space, otherwise
            // add one line of padding and the rest as the number of lines
            let lines = if content.is_empty() { 0 } else { content.lines().count() + 1 };

            title.is_some() as usize + lines
        } else {
            1 // one for the title
        }
    }

    /// Compute the width of the box based on the length of the
    /// [BoxContent].
    ///
    /// N.B. this counts the surrounding single character padding.
    pub fn width(&self) -> usize {
        match self {
            BoxContent::Content { title, content } => {
                let title_len = title.as_ref().map(|t| t.len()).unwrap_or(0);
                let content_len = content.lines().map(|l| l.len()).max().unwrap_or(0);
                title_len.max(content_len) + 2
            }
            BoxContent::Pad { size } => format!("{size} pad").len() + 2,
            BoxContent::Empty { width } => *width,
        }
    }

    /// Get the line at the given position in the box. If the function
    /// returns [`None`], then the line is empty, and the default padding
    /// should be used instead.
    pub fn line_at(&self, pos: usize) -> Option<String> {
        match self {
            BoxContent::Content { title, content } => {
                let title = title.as_ref().map(|t| t.as_str());

                if let Some(title) = title {
                    if pos == 0 {
                        return Some(title.to_string());
                    } else if pos == 1 {
                        return None;
                    }

                    // We have to account for the title, and the spacing between the title.
                    content.lines().nth(pos - 2).map(|line| line.to_string())
                } else {
                    content.lines().nth(pos).map(|line| line.to_string())
                }
            }
            BoxContent::Pad { size } => {
                if pos == 0 {
                    Some(format!("{size} pad"))
                } else if pos == 1 {
                    None
                } else {
                    Some("##".to_string())
                }
            }
            BoxContent::Empty { .. } => None,
        }
    }

    /// Compute the line contents at the given position. If the line is
    /// "empty", the function will return a string of spaces of the given
    /// width or use the box width.
    pub fn line_contents(&self, pos: usize, width: Option<usize>) -> String {
        let contents_or_empty = self.line_at(pos);
        let width = width.unwrap_or(self.width());

        if let Some(contents) = contents_or_empty {
            format!("{contents:^width$}")
        } else {
            " ".repeat(width)
        }
    }
}

/// A row of boxes that are printed in a single line.
#[derive(Debug)]
pub struct BoxRow {
    /// The contents of each box in the row.
    pub contents: Vec<BoxContent>,

    /// The computed widths of each box in the row. These are stored
    /// separately since they may be adjusted by the printer in order
    /// to align the boxes.
    pub widths: Vec<usize>,

    /// The max height of the row. This is used to determine the height
    /// of the row.
    pub max_height: usize,
}

impl BoxRow {
    /// Create a new [BoxRow] with the given contents.
    pub fn new(contents: Vec<BoxContent>) -> Self {
        let widths = contents.iter().map(|c| c.width()).collect();
        let max_height = contents.iter().map(|c| c.height()).max().unwrap_or(1);

        Self { contents, widths, max_height }
    }

    /// Get the "actual" width of the whole row. This will
    /// sum all of the widths and add the padding for each
    /// box in the row.
    pub fn width(&self) -> usize {
        self.widths.iter().sum::<usize>() + self.widths.len() + 1
    }

    /// Get the width of a[BoxContent] at the given index.
    pub fn width_at(&self, index: usize) -> Option<usize> {
        self.widths.get(index).copied()
    }

    /// Set the width of a [BoxContent] at the given index.
    pub fn set_width_at(&mut self, index: usize, width: usize) {
        if let Some(w) = self.widths.get_mut(index) {
            *w = width;
        }
    }

    /// Potentially adjust the width of the [BoxRow] to fit the given
    /// width.
    ///
    /// N.B. If the width of this [BoxRow] is greater than the desired
    /// width, this function will not do anything.
    fn adjust_to_width(&mut self, width: usize) {
        let current_width = self.width();

        if current_width == width {
            return;
        }

        // Insert an empty box to fill in the missing gap.
        if width - current_width > 2 {
            let empty_width = width - current_width - 1;
            self.widths.push(empty_width);
            self.contents.push(BoxContent::new_empty(empty_width));
        } else {
            // The row box doesn't need padding, but the
            // last box in the row will need it's width to be adjusted.
            let last_width = self.widths.len() - 1;
            self.widths[last_width] += width - current_width;
        }
    }
}

/// Represents the kind of connector that is being used to
/// join up two rows.
#[derive(Debug, Clone, Copy)]
pub enum ConnectorKind {
    /// Connector that is shared between two rows, i.e. `┼`
    Shared,

    /// Connector that faces up, i.e. `┴`
    Up,

    /// Connector that faces down, i.e. `┬`
    Down,
}

impl ConnectorKind {
    /// Check whether another [ConnectorKind] is on the same
    /// "level" as this one.
    pub fn is_same_level(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (_, Self::Shared) | (Self::Shared, _) | (Self::Down, Self::Down) | (Self::Up, Self::Up)
        )
    }
}

/// Represents a connector that is used to join up two rows.
#[derive(Debug, Clone, Copy)]
pub struct Connector {
    /// The kind of connector that is being used.
    pub kind: ConnectorKind,

    /// The symbol that should be used to print this
    /// particular connector.
    symbol: char,

    /// The width of the connector up to the next connector.
    offset: usize,
}

impl fmt::Display for Connector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol)
    }
}

struct LayoutWriterHelper<'l> {
    config: &'l LayoutWriterConfig,
}

impl LayoutWriterHelper<'_> {
    /// Write a "top" or "bottom" edge of the provided box collections. This
    /// function takes a collection of widths which represent the internal
    /// widths of the boxes that are being printed.
    pub fn write_box_horizontal_edge(
        &self,
        f: &mut fmt::Formatter<'_>,
        top: bool,
        widths: &[usize],
    ) -> fmt::Result {
        let max = (1, widths.len());
        let row_pos = if top { 0 } else { 1 };

        // we need to print the top edge of the box, which is just a line
        // of `+` characters, with the width of the box being the width
        // of the box, plus 2 for the padding.
        for (index, width) in widths.iter().copied().enumerate() {
            let pos = (row_pos, index);
            write!(
                f,
                "{}{}",
                self.config.connector(pos, max),
                iter::repeat(self.config.horizontal).take(width).collect::<String>()
            )?;
        }

        // we have to write the end of the box...
        writeln!(f, "{}", self.config.connector((row_pos, widths.len()), max))
    }

    fn compute_connectors(&self, widths: &[usize], from_top: bool) -> Vec<Connector> {
        let row = if from_top { 0 } else { 1 };
        let kind = if from_top { ConnectorKind::Down } else { ConnectorKind::Up };

        let max = (1, widths.len());
        let mut current_offset = 1;

        let mut connectors = vec![];

        for (index, width) in widths.iter().enumerate() {
            let pos = (row, index); // we assume that we are the top row...

            connectors.push(Connector {
                kind,
                symbol: self.config.connector(pos, max),
                offset: current_offset,
            });

            // One character for the connector, and the rest of the width
            current_offset += width + 1;

            // If we are not the last connector, we need to add a connector
            // to the collection.
            if index == widths.len() - 1 {
                let pos = (row, index + 1);

                connectors.push(Connector {
                    kind,
                    symbol: self.config.connector(pos, max),
                    offset: current_offset,
                });
            }
        }

        connectors
    }

    /// Draw a connecting horizontal edge between two box rows. This means that
    /// we have to handle connectors that are in the middle of the box, which
    /// might be connected in different points to the other boxes.
    pub fn write_central_horizontal_edge(
        &self,
        f: &mut fmt::Formatter<'_>,
        first_widths: &[usize],
        next_widths: &[usize],
    ) -> fmt::Result {
        // We store a collection of connectors, with the "connector" kind, and then the
        // offset that it exists at. Firstly, we populate the collection with the
        // connectors from the top width, and then we perform another pass to
        // "adjust" the existing connectors, and to insert the connectors from
        // the bottom widths.

        // Top ideas only...
        let top = self.compute_connectors(first_widths, false);
        let bottom = self.compute_connectors(next_widths, true);

        let max_offset = top.last().unwrap().offset;
        let mut merged_connectors = top;

        // Now we merge the bottom connectors...
        for bottom_connector in bottom.iter() {
            let current_offset = bottom_connector.offset;
            let index =
                merged_connectors.iter().position(|connector| connector.offset >= current_offset);

            if let Some(offset_index) = index {
                // If we have hit an intersection with another connector,
                // we need to replace the connector with a cross connector.
                if merged_connectors[offset_index].offset == current_offset {
                    merged_connectors[offset_index] = Connector {
                        kind: ConnectorKind::Shared,
                        // the offsets always start at 1
                        symbol: match current_offset {
                            1 => self.config.center_left,
                            _ if current_offset == max_offset => self.config.center_right,
                            _ => self.config.center,
                        },
                        offset: current_offset,
                    };
                } else {
                    // Otherwise, we need to insert the connector into the collection.
                    merged_connectors.insert(offset_index, *bottom_connector);
                }
            } else {
                // Otherwise, we need to insert the connector into the collection.
                merged_connectors.push(*bottom_connector);
            }
        }

        // Now we write the connectors to the formatter.
        for connector_pair in merged_connectors.windows(2) {
            let [first, second] = connector_pair else { unreachable!() };

            // Subtract one since we don't actually care about the "connector"
            // symbol.
            let spaces = (second.offset - first.offset) - 1;

            write!(
                f,
                "{}{}",
                first.symbol,
                iter::repeat(self.config.horizontal).take(spaces).collect::<String>()
            )?;
        }

        // Write the last connector
        writeln!(f, "{}", merged_connectors.last().unwrap().symbol)
    }
}

/// The [LayoutWriter] is a wrapper around [LayoutCtx] that allows
/// for the pretty printing of a [Layout] in a human readable format.
pub struct LayoutWriter<'l> {
    /// The layout and associated [ReprTy] to be written.
    pub ty_info: TyInfo,

    /// The current context for printing the layout. The [LayoutComputer]
    /// is needed since we want access to the interned types and layouts.
    pub ctx: LayoutComputer<'l>,

    /// A config that stores all of the characters that are used to
    /// draw the layout.
    pub config: LayoutWriterConfig,
}

impl<'l> LayoutWriter<'l> {
    /// Create a new [LayoutWriter] with a config.
    pub fn new_with_config(
        ty_info: TyInfo,
        ctx: LayoutComputer<'l>,
        config: LayoutWriterConfig,
    ) -> Self {
        Self { ty_info, ctx, config }
    }

    /// Create a new [LayoutWriter] that will write the given [Layout] to the
    /// given [fmt::Formatter] using "unicode" characters.
    pub fn new(ty_info: TyInfo, ctx: LayoutComputer<'l>) -> Self {
        Self { ty_info, ctx, config: LayoutWriterConfig::unicode() }
    }

    /// Create a new [LayoutWriter] that will write the given [Layout] to the
    /// given [fmt::Formatter] using "ascii" characters.
    pub fn new_ascii(ty_info: TyInfo, ctx: LayoutComputer<'l>) -> Self {
        Self { ty_info, ctx, config: LayoutWriterConfig::ascii() }
    }

    /// Perform a mapping over the [ReprTy] and [Layout] associated with
    /// this [LayoutWriter].
    fn with_info<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Self, &ReprTy, &Layout) -> T,
    {
        self.ty_info.ty.map(|ty| self.ty_info.layout.map(|layout| f(self, ty, layout)))
    }

    ///
    pub fn create_box_contents_for_shape(&self) -> Vec<BoxContent> {
        self.with_info(|this, ty, layout| this.create_box_contents(ty, layout, None))
    }

    /// Create all of the [BoxContent]s that represent the inner layout of a
    /// variant within the [LayoutShape].
    ///
    /// N.B. This inserts an initial box at the start of each row to identify
    /// the variant of the enum.
    pub fn create_box_contents_for_variant(
        &self,
        variant: VariantIdx,
        tag_size: Size,
        tag_box: BoxContent,
        col_width: usize,
        layout: LayoutId,
    ) -> BoxRow {
        self.ty_info.ty.map(|ty| {
            let mut contents = layout
                .map(|layout| self.create_box_contents(ty, layout, Some((tag_size, variant))));

            contents.insert(0, tag_box);

            let mut row = BoxRow::new(contents);
            row.set_width_at(0, col_width);
            row
        })
    }

    /// Create labels for the [LayoutShape], including size and
    /// offset labels.
    ///
    /// N.B. When creating content for [`Variants::Multiple`], the "variant"
    /// value must be provided in order to access the correct variant when
    /// computing box content.
    fn create_box_contents(
        &self,
        ty: &ReprTy,
        layout: &Layout,
        variant: Option<(Size, VariantIdx)>,
    ) -> Vec<BoxContent> {
        let mut boxes = Vec::new();

        let singular_box_content = || {
            format!(
                "  size: {}\noffset: {}\n align: {}",
                layout.size,
                Size::ZERO,
                layout.alignment.abi
            )
        };

        // If the layout is a `ZST`, then we just return a single box
        // with the layout, and a `<ZST>` label
        if layout.is_zst() {
            boxes.push(BoxContent::new(format!("<ZST>: {}", ty), singular_box_content()));
            return boxes;
        }

        match &layout.shape {
            // Reasonably trivial case where we just have a primitive,
            // here we just put the `size` and `offset` as the label.
            LayoutShape::Primitive => {
                boxes.push(BoxContent::new("primitive".to_string(), singular_box_content()));
            }
            LayoutShape::Union { count } => {
                // @@Todo: could there be a better title string for a
                // union primitive?
                boxes.push(BoxContent::new(format!("union{count}"), singular_box_content()));
            }
            LayoutShape::Array { stride, elements } => {
                boxes.push(BoxContent::new(
                    format!("[{stride}; {elements}]"),
                    singular_box_content(),
                ));
            }
            // Loop over all of the offsets, and then add content
            // boxes for each field, with the title being the name
            // of the field, and the type of the field in the form
            // of `<field: ty>`. The type of the field is printed
            // in minimal form.
            LayoutShape::Aggregate { fields, .. } => {
                // Load in the fields of the aggregate, however, this depends
                // on the type that is being stored.
                let field_titles = match (layout.abi, ty) {
                    (_, ReprTy::Adt(adt)) => {
                        adt.map(|adt| {
                            // we load in the variant that is specified in the
                            // "layouts" of the type.
                            let variant = match layout.variants {
                                Variants::Single { index } => index,
                                Variants::Multiple { .. } => {
                                    variant.map(|(_, variant)| variant).unwrap()
                                }
                            };

                            adt.variant(variant)
                                .fields
                                .clone()
                                .into_iter()
                                .map(|field| (field.name, format!("{}", field.ty)))
                                .collect::<Vec<_>>()
                        })
                    }
                    (AbiRepresentation::Scalar(scalar), _) => {
                        vec![(Identifier::num(0), format!("{scalar}"))]
                    }
                    (AbiRepresentation::Pair(scalar_1, scalar_2), _) => {
                        vec![
                            (Identifier::num(0), format!("{scalar_1}")),
                            (Identifier::num(1), format!("{scalar_2}")),
                        ]
                    }
                    _ => unreachable!(),
                };

                // The current computed size of the aggregate disregarding the last padding
                // on the field (if any).
                let mut current_size = Size::ZERO;
                let tag_size = variant.map(|(tag_size, _)| tag_size).unwrap_or(Size::ZERO);

                for (order_index, offset_index) in
                    layout.shape.iter_increasing_offsets().enumerate()
                {
                    let FieldLayout { offset, size } = fields[offset_index];

                    // we skip the first field, as the padding before this field
                    // maybe as the result of being within a variant, and therefore
                    // the padding will be handled by the variant printing.
                    let true_offset = if order_index == 0 { offset - tag_size } else { offset };

                    if current_size < true_offset {
                        let pad_size = true_offset - current_size;

                        // we need to add this as padding to the content
                        boxes.push(BoxContent::new_pad(pad_size));
                    }

                    boxes.push(BoxContent::new(
                        format!(
                            "{}: {}",
                            field_titles[offset_index].0, field_titles[offset_index].1
                        ),
                        format!(
                            "  size: {}\noffset: {}\n align: {}",
                            size, offset, layout.alignment.abi
                        ),
                    ));

                    current_size = offset + size;
                }

                // If the `current_size` isn't equal to the size of the layout, then
                // we need to add padding box to the content.
                if current_size != Size::ZERO && current_size < layout.size {
                    let pad_size = layout.size - current_size;

                    // we need to add this as padding to the content
                    boxes.push(BoxContent::new_pad(pad_size));
                }
            }
        }

        boxes
    }

    /// For multi-variant layouts, we want to create a row that represents
    /// the tag of the variant. This function will construct the tag variant
    /// and return the [BoxRow] for this.
    fn compute_tag_box_row(&self, tag_ty: IntTy, tag_size: Size, layout: &Layout) -> BoxRow {
        let offset = layout.shape.offset(0);

        if tag_size < offset {
            // we need to print the tag box first, and then the
            // variants.
            BoxRow::new(vec![
                BoxContent::new(format!("{tag_size} tag ({tag_ty})"), "".to_string()),
                BoxContent::new_pad(offset - tag_size),
            ])
        } else {
            BoxRow::new(vec![BoxContent::new(format!("{tag_size} tag ({tag_ty})"), "".to_string())])
        }
    }
}

impl fmt::Display for LayoutWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ty_info.layout.map(|layout| {
            // print the starting line of the layout.
            writeln!(
                f,
                "Layout of `{}` (size={} align={}):",
                self.ty_info.ty, layout.size, layout.alignment.abi
            )?;

            // Firstly, we print the initial "shape" of the
            // layout in order to account for the fact that
            // the layout may contain "multiple" variants that
            // are present in the layout, which we will also have to print.
            match layout.variants {
                Variants::Single { index: _ } => {
                    // this is the simple case, we merely need to print the
                    // boxes in a single row.
                    let content_boxes = self.create_box_contents_for_shape();
                    let max_height = content_boxes
                        .iter()
                        .map(|box_content| box_content.height())
                        .max()
                        .unwrap_or(1);
                    let box_widths: Vec<_> =
                        content_boxes.iter().map(|box_content| box_content.width()).collect();

                    let helper = LayoutWriterHelper { config: &self.config };

                    helper.write_box_horizontal_edge(f, true, &box_widths)?;

                    for line in 0..max_height {
                        // write the vertical connector
                        write!(f, "{}", self.config.vertical)?;

                        for (content_box, width) in content_boxes.iter().zip(box_widths.iter()) {
                            // write the line at the box, and align it to the maximum width of
                            // the box.
                            if let Some(line_contents) = content_box.line_at(line) {
                                write!(f, "{:^width$}{}", line_contents, self.config.vertical,)?;
                            } else {
                                write!(f, "{}{}", " ".repeat(*width), self.config.vertical)?;
                            }
                        }
                        writeln!(f)?;
                    }

                    helper.write_box_horizontal_edge(f, false, &box_widths)?;
                    Ok(())
                }
                Variants::Multiple { tag, field: _, ref variants } => {
                    let tag_ty = tag.kind().int_ty();
                    let tag_size = tag.size(self.ctx.data_layout());
                    let mut tag_row = self.compute_tag_box_row(tag_ty, tag_size, layout);
                    let mut tag_boxes = index_vec![];

                    // Compute the initial column width, accounting for the top
                    // box, and for the all of the variants that are present.
                    let mut tag_box_width = tag_row.width_at(0).unwrap();

                    self.ty_info.ty.map(|ty| {
                        for variant in ty.as_adt().borrow().variants.iter() {
                            // We want to read the discriminant value, and the variant name
                            // for the variant that we are printing.
                            let tag_box = BoxContent::new(
                                variant.name.to_string(),
                                variant.discriminant.to_string(self.ctx.data_layout().pointer_size),
                            );

                            tag_box_width = tag_box_width.max(tag_box.width());
                            tag_boxes.push(tag_box);
                        }
                    });

                    // In the event that the children of the tag box were bigger, then we increase
                    // the size of the box
                    tag_row.set_width_at(0, tag_box_width);

                    // firstly, deal with the tag box which is just essentially,
                    // a title with the size of the tag, possible padding and then
                    // the variants proceed after it.
                    let mut content_table = iter::once(tag_row)
                        .chain(variants.iter_enumerated().map(|(index, layout)| {
                            self.create_box_contents_for_variant(
                                index,
                                tag_size,
                                tag_boxes[index].clone(),
                                tag_box_width,
                                *layout,
                            )
                        }))
                        .collect::<Vec<_>>();

                    // Now, we might need to adjust the last content boxes in order to
                    // account for the fact that these boxes might be smaller than the
                    // largest row length, and thus have to ve grown or table padding
                    // is needed. So, for every row, we compute the "action" that is
                    // needed when printing the row.
                    //
                    // If the different between this row and the largest is <= 1, then
                    // we will adjust the width of the last box to account for the missing
                    // gap.
                    let row_widths: Vec<_> = content_table.iter().map(|row| row.width()).collect();
                    let max_row_width = *row_widths.iter().max().unwrap_or(&0);

                    for row in &mut content_table {
                        row.adjust_to_width(max_row_width)
                    }

                    debug_assert!(content_table.iter().all(|row| { row.width() == max_row_width }));

                    let helper = LayoutWriterHelper { config: &self.config };

                    // First draw the horizontal edge of the start
                    helper.write_box_horizontal_edge(f, true, &content_table[0].widths)?;

                    let write_row = |f: &mut fmt::Formatter<'_>, row: &BoxRow| -> fmt::Result {
                        for line in 0..row.max_height {
                            for (index, content_box) in row.contents.iter().enumerate() {
                                write!(
                                    f,
                                    "{}{}",
                                    self.config.vertical,
                                    content_box.line_contents(line, row.width_at(index))
                                )?;
                            }

                            writeln!(f, "{}", self.config.vertical)?;
                        }

                        Ok(())
                    };

                    for content_rows in content_table.windows(2) {
                        let (current_row, next_row) = (&content_rows[0], &content_rows[1]);

                        write_row(f, current_row)?;

                        // Write the connecting edge between the two rows, accounting for
                        // connectors intersecting with the central edge.
                        helper.write_central_horizontal_edge(
                            f,
                            &current_row.widths,
                            &next_row.widths,
                        )?;
                    }

                    // we need to write the final row of the table
                    write_row(f, content_table.last().unwrap())?;

                    helper.write_box_horizontal_edge(
                        f,
                        false,
                        &content_table.last().unwrap().widths,
                    )?;

                    Ok(())
                }
            }
        })
    }
}
