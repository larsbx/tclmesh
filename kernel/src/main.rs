use serde_json::Value;
use std::{fs, io::Read, process::ExitCode};
use tclmesh_kernel::conformance::{self, Relation};
use tclmesh_kernel::{evaluate, outcome};

const USAGE: &str = "usage: tclmesh-kernel evaluate < input.json\n       tclmesh-kernel conform VECTORS EXPECTED [--exact | --min-agreement RATIO]";

fn load(path: &str) -> Result<Value, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    serde_json::from_str(&text).map_err(|e| format!("{path}: {e}"))
}

fn run(args: &[String]) -> Result<bool, String> {
    match args {
        [cmd] if cmd == "evaluate" => {
            let mut text = String::new();
            std::io::stdin()
                .read_to_string(&mut text)
                .map_err(|e| e.to_string())?;
            let input: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
            let result = evaluate(
                input["action_id"].as_str().unwrap_or(""),
                &input["descriptor"],
                &input["state"],
                &input["request"],
            );
            println!("{}", outcome(&result));
            Ok(true)
        }
        [cmd, vectors, expected, rest @ ..] if cmd == "conform" => {
            let (relation, min): (Relation, f64) = match rest {
                [] => (Relation::Refines, 0.0),
                [flag] if flag == "--exact" => (Relation::Exact, 1.0),
                [flag, ratio] if flag == "--min-agreement" => (
                    Relation::Refines,
                    ratio.parse().map_err(|_| USAGE.to_owned())?,
                ),
                _ => return Err(USAGE.to_owned()),
            };
            let report = conformance::check(&load(vectors)?, &load(expected)?, relation);
            for v in &report.violations {
                eprintln!("VIOLATION {v}");
            }
            let total = report.total().max(1);
            let ratio = report.agreed as f64 / total as f64;
            println!(
                "{} vectors: {} agreed, {} refused (fail closed), {} violations; agreement {:.3}",
                report.total(),
                report.agreed,
                report.refused,
                report.violations.len(),
                ratio
            );
            if !report.refusals.is_empty() {
                println!("refusals by reason: {:?}", report.refusals);
            }
            if ratio < min {
                eprintln!("agreement {ratio:.3} below required {min}");
            }
            Ok(report.violations.is_empty() && report.total() > 0 && ratio >= min)
        }
        _ => Err(USAGE.to_owned()),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}
