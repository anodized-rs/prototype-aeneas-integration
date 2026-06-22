/**
 * Run the extraction pipeline (Charon -> Aeneas) on a SINGLE example crate.
 *
 * Usage:
 *   npm run translate e01                 (bare crate name; no `--` needed)
 *   npm run translate e01 -- --print-llbc (extra flags are forwarded to charon; `--` required)
 *
 * Always runs aeneas with `-emit-json` (writes the translation.json manifest).
 *
 * Output lands shallow in the crate folder, alongside `src/`:
 *   examples/<crate>/translation.lean         (umbrella)
 *   examples/<crate>/translation/Funs.lean    etc.
 *   examples/<crate>/translation/translation.json
 *
 * The multi-segment aeneas subdir `examples/<crate>/translation` makes the Lean module
 * prefix `examples.<crate>.translation`, which keeps every crate's modules unique under the
 * single central lake library (see lakefile.toml).
 *
 * Binaries are resolved from the locally-built `.aeneas/` (run `npm run aeneas-install`
 * first), falling back to PATH.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { findBinary } from "./lib/paths.js";
import { runStreaming } from "./lib/shell.js";

export const EXAMPLES_DIR = "examples";

/**
 * Run charon + aeneas on a single crate (e.g. "e01").
 * `root` is the repo root; `charonExtra` are forwarded to charon.
 */
export async function extractCrate(
  crate: string,
  root: string,
  charonExtra: string[] = [],
): Promise<void> {
  const crateDir = path.join(root, EXAMPLES_DIR, crate);
  if (!fs.existsSync(path.join(crateDir, "Cargo.toml"))) {
    throw new Error(`Crate not found: ${EXAMPLES_DIR}/${crate}/Cargo.toml`);
  }

  const pkgName = crate.replace(/-/g, "_");
  const llbcFile = `${pkgName}.llbc`;
  // POSIX-style subdir: aeneas turns the path separators into the Lean module prefix.
  const subdir = `${EXAMPLES_DIR}/${crate}/translation`;
  const outDir = path.join(crateDir, "translation");
  const umbrella = path.join(crateDir, "translation.lean");

  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);
  if (!charonBin) throw new Error("Charon not found. Run 'npm run aeneas-install' first.");
  if (!aeneasBin) throw new Error("Aeneas not found. Run 'npm run aeneas-install' first.");

  console.log(chalk.bold(`\nExtracting ${EXAMPLES_DIR}/${crate} -> ${subdir}\n`));

  // ── Step 1: Charon (Rust -> LLBC) ───────────────────────────────────
  console.log(chalk.bold("Step 1: Charon..."));
  const llbcPath = path.join(crateDir, llbcFile);
  if (fs.existsSync(llbcPath)) fs.unlinkSync(llbcPath);

  // `--dest crateDir` is required: in a Cargo workspace Charon otherwise writes the llbc to
  // the workspace root, not the crate's own directory.
  await runStreaming(
    charonBin,
    ["cargo", "--preset=aeneas", "--dest", crateDir, ...charonExtra],
    { cwd: crateDir },
  );

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Charon did not produce ${EXAMPLES_DIR}/${crate}/${llbcFile}`);
  }
  console.log(chalk.green(`  LLBC: ${EXAMPLES_DIR}/${crate}/${llbcFile}\n`));

  // ── Step 2: Aeneas (LLBC -> Lean + JSON) ────────────────────────────
  console.log(chalk.bold("Step 2: Aeneas (-emit-json)..."));
  fs.rmSync(outDir, { recursive: true, force: true });
  fs.rmSync(umbrella, { force: true });

  await runStreaming(
    aeneasBin,
    [llbcPath, "-backend", "lean", "-dest", root, "-subdir", subdir, "-split-files", "-emit-json"],
    { cwd: root },
  );

  // ── Step 3: Drop the _Template suffix (match existing convention) ────
  for (const f of fs.readdirSync(outDir)) {
    if (f.endsWith("_Template.lean")) {
      fs.renameSync(path.join(outDir, f), path.join(outDir, f.replace("_Template", "")));
    }
  }

  // ── Step 4: Move translation.json into the crate's translation/ folder ──
  // Aeneas writes it to `-dest` (the repo root). Keep every artifact for a crate together,
  // and fix the now-renamed _Template paths.
  const jsonSrc = path.join(root, "translation.json");
  if (fs.existsSync(jsonSrc)) {
    const json = fs.readFileSync(jsonSrc, "utf-8").replaceAll("_Template.lean", ".lean");
    fs.writeFileSync(path.join(outDir, "translation.json"), json, "utf-8");
    fs.unlinkSync(jsonSrc);
  }

  console.log(chalk.green(`\nDone. Lean files + translation.json in ${EXAMPLES_DIR}/${crate}/translation/`));
}

function usage(msg?: string): never {
  if (msg) console.error(chalk.red(msg));
  console.error("Usage: npm run translate <crate> [-- charon flags...]");
  console.error("  e.g. npm run translate e01");
  console.error("       npm run translate e01 -- --print-llbc");
  process.exit(1);
}

async function main(): Promise<void> {
  const root = process.cwd();
  const argv = process.argv.slice(2);

  // First non-flag arg is the crate; everything else is forwarded to charon.
  const crate = argv.find((a) => !a.startsWith("-"));
  const charonExtra = argv.filter((a) => a.startsWith("-"));
  if (!crate) usage("No crate specified.");

  await extractCrate(crate, root, charonExtra);
}

// Only run main() when invoked directly, not when imported by extract-all.
if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch((err) => {
    console.error(chalk.red(`\nError: ${err.message}`));
    process.exit(1);
  });
}
