use std::{
	fmt::Debug,
	fs,
	io::Write,
	path::{Path, PathBuf},
};

use uxnsmal::error;

/// Trait for a "text tester" structure
/// This structure will be instanciated for each file in the specified test directory
pub trait TextTester {
	type Type: Debug;

	fn new() -> Self;
	fn test(&mut self, source: &str) -> Option<error::Result<Self::Type>>;
}

fn write_tmp(path: &Path, content: &str) -> PathBuf {
	let tmp_dir_path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
	let mut tmp_path = tmp_dir_path.join(&path.file_name().unwrap());
	tmp_path.set_extension("smal.txt");

	let mut file = fs::File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open(&tmp_path)
		.unwrap_or_else(|e| panic!("unable to open {tmp_path:?}: {e}"));

	file.write_all(content.as_bytes())
		.unwrap_or_else(|e| panic!("unable to write temporary file {tmp_path:?}: {e}"));

	tmp_path
}

pub fn make_text_tests<T: TextTester>(dir_path: impl AsRef<Path>) {
	let dir_path = dir_path.as_ref();
	let dir =
		fs::read_dir(&dir_path).unwrap_or_else(|e| panic!("unable to read {dir_path:?} dir: {e}"));

	println!();

	for entry in dir {
		let entry = entry.expect("unable to get dir entry");
		let path = entry.path();
		let typ = entry
			.file_type()
			.unwrap_or_else(|e| panic!("unable to read {path:?} type: {e}"));

		if !typ.is_file() {
			continue;
		}

		if path.extension().is_some_and(|e| e == "txt") {
			continue;
		}

		handle_file::<T>(path);
	}

	println!();
}

#[inline(always)]
fn handle_file<T: TextTester>(path: PathBuf) {
	let source = fs::read_to_string(&path)
		.unwrap_or_else(|e| panic!("unable to read {path:?} contents: {e}"));

	let mut tester = T::new();
	let result = tester
		.test(&source)
		.expect("`test` must return at least one Some(Result)");

	let should_error = path
		.file_name()
		.unwrap()
		.to_str()
		.unwrap()
		.starts_with("err.");

	let mut output: String;

	// Collect output
	match &result {
		Ok(ok) if should_error => {
			// Expected Err, but got Ok
			let tmp_path = write_tmp(&path, &format!("{ok:#?}"));
			eprintln!("    failed: expected Err, but got Ok in {path:?}!");
			eprintln!("        see {tmp_path:?} for the output");
			panic!();
		}
		Err(e) if !should_error => {
			// Expected Ok, but got Err
			eprintln!("    failed: expected Ok, but got Err in {path:?}!");
			eprintln!("        error: {e:?}");
			panic!();
		}

		Ok(ok) => {
			output = format!("{ok:#?}");
		}
		Err(e) => {
			output = format!("{e:#?}\n");

			// Collect as many errors as possible
			while let Some(res) = tester.test(&source) {
				match res {
					Err(e) => output.push_str(&format!("{e:#?}\n")),
					Ok(ok) => {
						eprintln!("    failed: unexpected Ok result in {path:?}!");
						eprintln!("        result: {ok:#?}");
						panic!();
					}
				}
			}
		}
	}

	// Check for test expected output file existance
	let mut expected_path = path.clone();
	expected_path.set_extension("smal.txt");

	let expected_exists = fs::exists(&expected_path)
		.unwrap_or_else(|e| panic!("unable to check for existance of {expected_path:?}: {e}"));

	if expected_exists {
		let expected_output = fs::read_to_string(&expected_path).unwrap_or_else(|e| {
			panic!("unable to read test expected output file {expected_path:?}: {e}")
		});

		if expected_output == output {
			// Test passed
			match result {
				Ok(_) => println!("    passed: {path:?} passed Ok test"),
				Err(_) => println!("    passed: {path:?} passed Err test"),
			}
		} else {
			// Test failed
			let tmp_path = write_tmp(&path, &output);
			match result {
				Ok(_) => eprintln!("    failed: {path:?} did not pass Ok test!"),
				Err(_) => eprintln!("    failed: {path:?} did not pass Err test!"),
			}

			eprintln!("        note: delete this .txt file to regenerate the expected output");
			eprintln!("        see {tmp_path:?} for the output");

			panic!()
		}
	} else {
		// Generate an new "expected output" file
		fs::write(&expected_path, output)
			.unwrap_or_else(|e| panic!("unable to write test output into {expected_path:?}: {e}"));

		match result {
			Ok(_) => println!("    info: written Ok test output in {path:?}"),
			Err(_) => println!("    info: written Err test output in {path:?}"),
		}
	}
}
