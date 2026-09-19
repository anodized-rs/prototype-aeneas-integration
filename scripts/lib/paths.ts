import path from "node:path";
import fs from "node:fs";
import { execSync } from "node:child_process";

/**
 * Resolve a binary from the extracted aeneas release bundle, falling back to PATH.
 *
 * Bundle layout (see `npm run aeneas-install`):
 *   .aeneas/aeneas
 *   .aeneas/charon
 *   .aeneas/charon-driver
 *   .aeneas/rust-toolchain
 *   .aeneas/backends/...
 */
export function findBinary(name: "charon" | "aeneas", root: string): string | null {
  const local = path.join(root, ".aeneas", name);
  if (fs.existsSync(local)) return local;

  // Fall back to PATH
  try {
    const result = execSync(`which ${name}`, { encoding: "utf-8" }).trim();
    return result || null;
  } catch {
    return null;
  }
}
