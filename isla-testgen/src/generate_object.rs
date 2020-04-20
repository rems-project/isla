use crate::extract_state;

use faerie::*;
use target_lexicon::triple;
use std::fs::File;
use std::path::Path;
use std::str::FromStr;

pub fn make_file(file_name: String, initial_state: extract_state::InitialState) -> Result<(), Box<dyn std::error::Error>> {
    let file = File::create(Path::new(&file_name))
        .expect("Unable to create file");
    let mut object = ArtifactBuilder::new(triple!("aarch64-unknown-unknown-elf"))
        .name(file_name.to_owned())
        .finish();

    let mut name = 0;
    for (region, contents) in initial_state.memory.iter() {
        object.declare_with(format!("data{}", name), Decl::data().writable(), contents.clone())?;
        name += 1;
    }

    name = 0;
    for (region, contents) in initial_state.code.iter() {
        object.declare_with(format!("code{}", name), Decl::function(), contents.clone())?;
        name += 1;
    }

    object.write(file)?;

    Ok(())
}
