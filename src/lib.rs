mod bytecode;
mod cfg;
mod error;
mod expr;
mod loader;
mod lowering;
mod normalize;
mod structure;
mod types;
mod writer;

use std::path::Path;

pub use error::{DecompileError, Result};

pub fn decompile_bytes(bytes: &[u8]) -> Result<String> {
    let reader = rust_asm::class_reader::ClassReader::new(bytes);
    let class_node = reader.to_class_node()?;
    let class = loader::load_class(class_node)?;
    Ok(writer::write_class(&class, None))
}

pub fn decompile_path(path: &Path) -> Result<String> {
    let bytes = std::fs::read(path)?;
    let reader = rust_asm::class_reader::ClassReader::new(&bytes);
    let class_node = reader.to_class_node()?;
    let class = loader::load_class(class_node)?;
    let resolver = lowering::ClassPathResolver::for_class_file(path, &class.internal_name);
    Ok(writer::write_class(&class, resolver.as_ref()))
}
