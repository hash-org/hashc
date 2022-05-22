//! All rights reserved 2022 (c) The Hash Language authors
use core::fmt;
use std::{borrow::Cow, iter};

/// A node in a tree, with a label and children.
#[derive(Debug, Clone)]
pub struct TreeNode {
    pub label: Cow<'static, str>,
    pub children: Vec<TreeNode>,
}

impl TreeNode {
    /// Create a leaf node with the given label.
    pub fn leaf(label: impl Into<Cow<'static, str>>) -> Self {
        Self {
            label: label.into(),
            children: vec![],
        }
    }

    /// Create a branch node with the given children.
    pub fn branch(label: impl Into<Cow<'static, str>>, children: Vec<TreeNode>) -> Self {
        Self {
            label: label.into(),
            children,
        }
    }
}

/// Configuration for [TreeWriter].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeWriterConfig {
    /// What to left-pad the tree with.
    pub pad: char,
    /// The code point to use for the vertical line drawing character.
    pub vertical_line: char,
    /// The code point to use for the middle intersection drawing character.
    pub middle_intersect: char,
    /// The code point to use for the end intersection drawing character.
    pub end_intersect: char,
    /// What to prefix the children with (first line).
    pub child_prefix: Cow<'static, str>,
}

impl TreeWriterConfig {
    /// Draw trees using Unicode box drawing characters.
    pub fn unicode() -> Self {
        Self {
            pad: ' ',
            vertical_line: '│',
            middle_intersect: '├',
            end_intersect: '└',
            child_prefix: "─".into(),
        }
    }

    /// Draw trees using Unicode box drawing characters and longer child prefixes.
    pub fn unicode_long() -> Self {
        Self {
            child_prefix: "──".into(),
            ..Self::unicode()
        }
    }

    /// Draw trees using ASCII characters.
    pub fn ascii() -> Self {
        Self {
            pad: ' ',
            vertical_line: '|',
            middle_intersect: '|',
            end_intersect: '`',
            child_prefix: "-".into(),
        }
    }

    /// Draw as an indented list, without vertical lines.
    pub fn list() -> Self {
        Self {
            pad: ' ',
            vertical_line: ' ',
            middle_intersect: ' ',
            end_intersect: ' ',
            child_prefix: "-".into(),
        }
    }
}

impl Default for TreeWriterConfig {
    fn default() -> Self {
        Self::unicode()
    }
}

/// Can print a tree through [fmt::Display], using a reference to a [TreeNode].
#[derive(Debug, Clone)]
pub struct TreeWriter<'t, 'cfg> {
    tree: &'t TreeNode,
    pad: String,
    config: Cow<'cfg, TreeWriterConfig>,
}

impl<'t, 'cfg> TreeWriter<'t, 'cfg> {
    /// Create a new [TreeWriter] with the given [TreeNode] and default configuration.
    pub fn new(tree: &'t TreeNode) -> Self {
        Self::new_with_config(tree, TreeWriterConfig::default())
    }

    /// Create a new [TreeWriter] with the given [TreeNode] and configuration [TreeWriterConfig].
    pub fn new_with_config(tree: &'t TreeNode, config: TreeWriterConfig) -> Self {
        Self {
            tree,
            pad: String::new(),
            config: Cow::Owned(config),
        }
    }

    fn is_last(&self, child_index: usize) -> bool {
        child_index == self.tree.children.len() - 1
    }

    fn next_depth(&self, child: &'t TreeNode, child_index: usize) -> TreeWriter {
        let vertical_line_or_pad = iter::once(if self.is_last(child_index) {
            self.config.pad
        } else {
            self.config.vertical_line
        });

        let extra_pad =
            iter::repeat(self.config.pad).take(self.config.child_prefix.chars().count());

        let new_pad = self
            .pad
            .chars()
            .chain(vertical_line_or_pad)
            .chain(extra_pad)
            .collect();

        TreeWriter {
            tree: child,
            pad: new_pad,
            config: Cow::Borrowed(self.config.as_ref()),
        }
    }
}

impl fmt::Display for TreeWriter<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", self.tree.label)?;

        for (index, child) in self.tree.children.iter().enumerate() {
            let pipe_char = if self.is_last(index) {
                self.config.end_intersect
            } else {
                self.config.middle_intersect
            };

            let child_writer = self.next_depth(child, index);

            write!(
                f,
                "{}{}{}{}",
                self.pad, pipe_char, self.config.child_prefix, child_writer,
            )?;
        }

        Ok(())
    }
}
