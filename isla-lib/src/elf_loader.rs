use std::collections::HashMap;
use std::fs;

use crate::memory::Memory;
use crate::concrete::BV;

use elfloader::*;

/// A simple ExampleLoader, that implements ElfLoader
/// but does nothing but logging
struct ExampleLoader<'ir, B: BV> {
    memory: &'ir mut Memory<B>
}

impl<'ir, B: BV> ElfLoader for ExampleLoader<'ir, B> {
    fn allocate(&mut self, load_headers: LoadableHeaders) -> Result<(), &'static str> {
        for header in load_headers {
            let base = header.virtual_addr();
            let end = base + header.mem_size();
            self.memory.add_concrete_region(base..end, HashMap::new());
            println!(
                "allocate base = {:#x} size = {:#x} flags = {}",
                header.virtual_addr(),
                header.mem_size(),
                header.flags()
            );
        }
        Ok(())
    }

    fn relocate(&mut self, _entry: &Rela<P64>) -> Result<(), &'static str> {
        unimplemented!()
    }

    fn load(&mut self, _flags: Flags, base: VAddr, region: &[u8]) -> Result<(), &'static str> {
        let start = base;
        let end = base + region.len() as u64;
        let mut i = 0;
        for b in region {
            self.memory.write_byte(start + i, *b);
            i += 1;
        }
        println!("load region into = {:#x} -- {:#x}", start, end);
        Ok(())
    }

    fn tls(
        &mut self,
        _tdata_start: VAddr,
        _tdata_length: u64,
        _total_size: u64,
        _align: u64
    ) -> Result<(), &'static str> {
        unimplemented!()
    }
}

pub fn load_elf<'ir, B: BV>(path: &str, memory: &'ir mut Memory<B>) {
    let binary_blob = fs::read(path).expect("Can't read binary");
    let binary = ElfBinary::new("test", binary_blob.as_slice()).expect("Got proper ELF file");
    let mut loader = ExampleLoader { memory: memory };
    binary.load(&mut loader).expect("Can't load the binary?");
}
