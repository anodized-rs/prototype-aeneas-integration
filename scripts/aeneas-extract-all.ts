/**
 * Run the extraction pipeline on EVERY example crate, one after the other.
 *
 * Usage:
 *   npm run translate-all                  translate every examples/* crate
 *   npm run translate-all -- --print-llbc  forward extra flags to charon (`--` required)
 *
 * Crates are discovered by globbing examples/<crate>/Cargo.toml. Fails fast, naming the
 * crate that broke.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { EXAMPLES_DIR, extractCrate } from "./aeneas-extract-one.js";

function discoverCrates(root: string): string[] {
  const examplesDir = path.join(root, EXAMPLES_DIR);
  if (!fs.existsSync(examplesDir)) return [];
  return fs
    .readdirSync(examplesDir, { withFileTypes: true })
    .filter((e) => e.isDirectory())
    .map((e) => e.name)
    .filter((name) => fs.existsSync(path.join(examplesDir, name, "Cargo.toml")))
    .sort();
}

async function main(): Promise<void> {
  const root = process.cwd();
  const charonExtra = process.argv.slice(2).filter((a) => a.startsWith("-"));

  const crates = discoverCrates(root);
  if (crates.length === 0) {
    console.error(chalk.red(`No crates found under ${EXAMPLES_DIR}/.`));
    process.exit(1);
  }

  console.log(chalk.bold(`Translating ${crates.length} crate(s): ${crates.join(", ")}`));

  for (const crate of crates) {
    console.log(chalk.bold.cyan(`\n${"=".repeat(60)}\n  ${crate}\n${"=".repeat(60)}`));
    try {
      await extractCrate(crate, root, charonExtra);
    } catch (err) {
      console.error(chalk.red(`\nFailed on crate "${crate}": ${(err as Error).message}`));
      process.exit(1);
    }
  }

  console.log(chalk.green(`\nAll ${crates.length} crate(s) translated.`));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
