use std::{
	fs,
	io::Write,
	path::{Path, PathBuf},
};

use uxnsmal::lexer::Lexer;

fn write_tmp(for_path: &Path, content: &str) -> PathBuf {
	let tmp_path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
	let mut tmp_output_path = tmp_path.join(&for_path.file_name().unwrap());
	tmp_output_path.set_extension("smal.txt");

	let mut file = fs::File::options()
		.write(true)
		.create(true)
		.open(&tmp_output_path)
		.unwrap_or_else(|e| panic!("unable to open {tmp_output_path:?}: {e}"));

	file.write_all(content.as_bytes())
		.unwrap_or_else(|e| panic!("unable to write test output into {tmp_output_path:?}: {e}"));

	tmp_output_path
}

#[test]
fn lexer_text_tests() {
	let dir_path = PathBuf::from("tests/lexer");
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

		// Read test file contents
		let content = fs::read_to_string(&path)
			.unwrap_or_else(|e| panic!("unable to read {path:?} contents: {e}"));

		let mut got_output: String;

		// Lex the test file
		let tokens = Lexer::lex(&content);

		let should_error = path
			.file_name()
			.unwrap()
			.to_str()
			.unwrap()
			.starts_with("error.");

		match tokens {
			Ok(t) if should_error => {
				let tmp_path = write_tmp(&path, &format!("{t:#?}"));

				eprintln!("    failed: expected Err, but got Ok for {path:?}!");
				eprintln!("        see \"{}\"", tmp_path.display());
				panic!();
			}
			Err(e) if !should_error => {
				eprintln!("    failed: expected Ok, but got Err for {path:?}!");
				eprintln!("        error: {e:?}");
				panic!();
			}

			Ok(ref t) => {
				got_output = format!("{t:#?}");
			}
			Err(ref e) => {
				got_output = format!("{e:#?}\n");

				let mut span_end: Option<usize> = e.span().map(|s| s.end);
				while let Some(some_end) = span_end {
					match Lexer::lex_with_skip(&content, some_end) {
						Ok(t) => {
							// No tokens, or only Eof
							if t.len() <= 1 {
								break;
							}

							eprintln!("    failed: unexpected Ok result for {path:?}!");
							eprintln!("        result: {t:#?}");
							eprintln!("        slice: {:#?}", &content[some_end..]);
							panic!();
						}
						Err(e) => {
							got_output.push_str(&format!("{e:#?}\n"));
							span_end = e.span().map(|s| s.end);
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

			if expected_output == got_output {
				match tokens {
					Ok(_) => println!("    passed: {path:?} passed Ok test"),
					Err(_) => println!("    passed: {path:?} passed Err test"),
				}
			} else {
				let tmp_path = write_tmp(&path, &got_output);

				eprint!("    failed: {path:?} did not pass test! ");
				match tokens {
					Ok(_) => eprintln!("Ok outputs doesn't match"),
					Err(_) => eprintln!("Err outputs doesn't match"),
				}

				eprintln!("        note: delete this .txt file to regenerate the expected output",);
				eprintln!("        see \"{}\" for the output", tmp_path.display(),);

				panic!()
			}
		} else {
			fs::write(&expected_path, got_output).unwrap_or_else(|e| {
				panic!("unable to write test output into {expected_path:?}: {e}")
			});

			match tokens {
				Ok(_) => println!("    info: written Ok output for {path:?}"),
				Err(_) => println!("    info: written Err output for {path:?}"),
			}
		}
	}

	println!();
}
