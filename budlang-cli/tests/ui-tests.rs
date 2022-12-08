use assert_cmd::Command;

#[test]
#[cfg_attr(miri, ignore)]
fn eval() {
    let mut cmd = Command::cargo_bin("bud").unwrap();
    let result = cmd.arg("1 + 2").assert().success();
    let result = std::str::from_utf8(&result.get_output().stdout).unwrap();
    assert_eq!(result, "3\n");
}

#[test]
#[cfg_attr(miri, ignore)]
fn pipe() {
    let mut cmd = Command::cargo_bin("bud").unwrap();
    let result = cmd.write_stdin("1 + 2").assert().success();
    let result = std::str::from_utf8(&result.get_output().stdout).unwrap();
    assert_eq!(result, "3\n");
}

#[test]
#[cfg_attr(miri, ignore)]
fn eval_and_pipe() {
    let mut cmd = Command::cargo_bin("bud").unwrap();
    let result = cmd.arg("1 + 2").write_stdin("3 + 4").assert().success();
    let result = std::str::from_utf8(&result.get_output().stdout).unwrap();
    assert_eq!(result, "3\n7\n");
}

#[test]
#[cfg_attr(miri, ignore)]
fn run_file() {
    std::fs::write(
        "run_file.bud",
        br#"
        function test(a, b)
            a + b
        end
    "#,
    )
    .unwrap();
    let mut cmd = Command::cargo_bin("bud").unwrap();
    let result = cmd
        .arg("-f")
        .arg("run_file.bud")
        .arg("test(1, 2)")
        .assert()
        .success();
    let result = std::str::from_utf8(&result.get_output().stdout).unwrap();
    assert_eq!(result, "3\n");
    std::fs::remove_file("run_file.bud").unwrap();
}
