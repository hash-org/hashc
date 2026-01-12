//! A module that contains the implementation to the
//! virtual machine memory model.
//!
//! Essentially, this is a wrapper on top a conceptual
//! memory space that the VM can use to read and write
//! data to/from.
//!
//! This "memory" space is a global view of the entire machine
//! state, i.e. it hosts the stack, heap, and static data segments.
//!
//! That way, we can have a unified address space for the VM to
//! read and write data to/from.

use std::iter::IntoIterator;

use hash_utils::{
    index_vec::{IndexVec, define_index_type, index_vec},
    itertools::Itertools,
    range_map::RangeMap,
};

use crate::error::RuntimeError;

define_index_type! {
    /// A unique identifier for a memory region.
    pub struct RegionId = u32;
    MAX_INDEX = i32::MAX as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

#[derive(Debug, Clone)]
pub struct Region {
    /// The unique identifier of the region.
    pub id: RegionId,

    /// The name of the region, usually pre-determined
    /// by the VM memory model.
    pub name: String,

    /// The start address of the memory region.
    pub start: usize,

    /// The size of the memory region.
    pub size: usize,

    /// Flags that should be applied to the memory region.
    pub flags: RegionFlags,
}

bitflags::bitflags! {
    /// Flags that can be applied to a memory region.
    ///
    /// Each flag implies that they have that particular
    /// and all lower permissions. For example, if a region
    /// has the `EXECUTE` flag, it also implies that it has
    /// the `READ` and `WRITE` flags.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct RegionFlags: u8 {
        /// Readable region.
        const READ = 1 << 0;

        /// Writable region.
        const WRITE = 1 << 1 | Self::READ.bits();

        /// Executable region.
        const EXECUTE = 1 << 2 | Self::WRITE.bits();
    }
}

/// The [MemoryBuilder] structure is used to abstract the
/// construction of a [Memory] instance. Overall, the idea
/// of the builder is that it is used to control and manage
/// individual memory regions, their sizes and properties,
/// and finally build the memory space that the VM will use.
#[derive(Debug, Default)]
pub struct MemoryBuilder {
    /// The region of the map being built.
    ///
    /// This will be the final region map once
    /// everything else has been built and finalised.
    region_map: RangeMap<usize, RegionId>,

    /// A list of the current regions that are being
    /// constructed.
    regions: IndexVec<RegionId, Region>,

    /// The current offset of where to begin the next
    /// region if we needed to re-size the memory.
    offset: usize,
}

impl MemoryBuilder {
    /// Create a new region builder.
    pub fn new() -> Self {
        Self { region_map: RangeMap::new(), regions: index_vec![], offset: 0 }
    }

    /// Add a new region to the region map.
    pub fn add_region(&mut self, name: String, size: usize, flags: RegionFlags) -> &mut Self {
        let offset = self.offset;
        let region =
            Region { id: RegionId::new(self.regions.len()), name, start: offset, size, flags };
        let start = offset + region.start;
        let end = offset + region.start + region.size.saturating_sub(1);

        self.region_map.insert(start..=end, region.id);
        self.offset = end + 1;
        self.regions.push(region);
        self
    }

    /// Finalize the region map.
    pub fn build(self) -> Memory {
        Memory {
            memory: vec![0; self.offset],
            region_map: RangeMap::populated(
                self.region_map
                    .into_iter()
                    .map(|pair| (pair.0, self.regions[pair.1].clone()))
                    .collect_vec(),
            ),
        }
    }
}

/// The default size of the stack region.
const DEFAULT_STACK_SIZE: usize = 100 * 1024;

/// The default size of the VM memory space.
///
/// 2MB stack by default.
const DEFAULT_SIZE: usize = 2 * 1024 * 1024;

/// A representation of the VM memory space.
///
/// This contains the actual memory bytes as well as
/// a region map that tracks the different memory regions
/// and their properties.
#[derive(Debug)]
pub struct Memory {
    /// The memory space of the VM.
    pub memory: Vec<u8>,

    /// A map of the region space that is being
    /// used within the VM.
    pub region_map: RangeMap<usize, Region>,
}

impl Memory {
    pub fn check_access(
        &self,
        addr: usize,
        size: usize,
        flags: RegionFlags,
    ) -> Result<(), RuntimeError> {
        let entry = self.region_map.find(addr).ok_or(RuntimeError::MemoryAccessViolation {
            addr,
            size,
            reason: "No memory region found for the given address".to_string(),
        })?;

        // Check if the memory can be written into this region
        if size > entry.size {
            return Err(RuntimeError::MemoryAccessViolation {
                addr,
                size,
                reason: format!(
                    "Access size {} exceeds region size {} for region {}",
                    size, entry.size, entry.name
                ),
            });
        }

        // Check if the region has the required flags. This accounts
        // for that if `flags` have
        let missing = entry.flags - flags;
        if missing > flags {
            return Err(RuntimeError::MemoryAccessViolation {
                addr,
                size,
                reason: format!(
                    "Region {} is missing required access flags: {:?}",
                    entry.name, missing
                ),
            });
        }

        Ok(())
    }
}

impl Default for Memory {
    fn default() -> Self {
        let mut builder = MemoryBuilder::new();
        builder
            .add_region(
                "read_only".to_string(),
                0, // We don't allocate any read-only data by default.
                RegionFlags::READ,
            )
            .add_region("stack".to_string(), DEFAULT_STACK_SIZE, RegionFlags::WRITE)
            .add_region("heap".to_string(), DEFAULT_SIZE, RegionFlags::WRITE);
        builder.build()
    }
}

pub trait HasMemoryAccess {
    /// Read and write methods for the VM memory.
    fn read8(&self, addr: usize) -> Result<&[u8; 1], RuntimeError>;
    fn read16(&self, addr: usize) -> Result<&[u8; 2], RuntimeError>;
    fn read32(&self, addr: usize) -> Result<&[u8; 4], RuntimeError>;
    fn read64(&self, addr: usize) -> Result<&[u8; 8], RuntimeError>;
    fn write8(&mut self, addr: usize, value: &[u8; 1]) -> Result<(), RuntimeError>;
    fn write16(&mut self, addr: usize, value: &[u8; 2]) -> Result<(), RuntimeError>;
    fn write32(&mut self, addr: usize, value: &[u8; 4]) -> Result<(), RuntimeError>;
    fn write64(&mut self, addr: usize, value: &[u8; 8]) -> Result<(), RuntimeError>;
}

impl HasMemoryAccess for Memory {
    fn read8(&self, addr: usize) -> Result<&[u8; 1], RuntimeError> {
        self.check_access(addr, 8, RegionFlags::READ)?;
        let value = self.memory[addr..addr + 1].try_into().unwrap();
        Ok(value)
    }

    fn read16(&self, addr: usize) -> Result<&[u8; 2], RuntimeError> {
        self.check_access(addr, 16, RegionFlags::READ)?;
        let value = self.memory[addr..addr + 2].try_into().unwrap();
        Ok(value)
    }

    fn read32(&self, addr: usize) -> Result<&[u8; 4], RuntimeError> {
        self.check_access(addr, 32, RegionFlags::READ)?;
        let value = self.memory[addr..addr + 4].try_into().unwrap();
        Ok(value)
    }

    fn read64(&self, addr: usize) -> Result<&[u8; 8], RuntimeError> {
        self.check_access(addr, 64, RegionFlags::READ)?;
        let value = self.memory[addr..addr + 8].try_into().unwrap();
        Ok(value)
    }

    fn write8(&mut self, addr: usize, value: &[u8; 1]) -> Result<(), RuntimeError> {
        self.check_access(addr, 8, RegionFlags::WRITE)?;
        self.memory[addr..addr + 1].copy_from_slice(value);
        Ok(())
    }

    fn write16(&mut self, addr: usize, value: &[u8; 2]) -> Result<(), RuntimeError> {
        self.check_access(addr, 16, RegionFlags::WRITE)?;
        self.memory[addr..addr + 2].copy_from_slice(value);
        Ok(())
    }

    fn write32(&mut self, addr: usize, value: &[u8; 4]) -> Result<(), RuntimeError> {
        self.check_access(addr, 32, RegionFlags::WRITE)?;
        self.memory[addr..addr + 4].copy_from_slice(value);
        Ok(())
    }

    fn write64(&mut self, addr: usize, value: &[u8; 8]) -> Result<(), RuntimeError> {
        self.check_access(addr, 64, RegionFlags::WRITE)?;
        self.memory[addr..addr + 8].copy_from_slice(value);
        Ok(())
    }
}
