import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";

export interface AeneasConfig {
  aeneas: {
    commit: string;
    repo: string;
  };
}

/**
 * Walk up from `from` to find the directory containing `aeneas-config.yml`.
 */
export function findProjectRoot(from?: string): string {
  let dir = from ?? process.cwd();
  while (true) {
    if (fs.existsSync(path.join(dir, "aeneas-config.yml"))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error("Could not find aeneas-config.yml in any parent directory");
    }
    dir = parent;
  }
}

/**
 * Load and validate aeneas-config.yml.
 */
export function loadConfig(root?: string): { config: AeneasConfig; root: string } {
  const projectRoot = root ?? findProjectRoot();
  const filePath = path.join(projectRoot, "aeneas-config.yml");

  if (!fs.existsSync(filePath)) {
    throw new Error(`Config file not found: ${filePath}`);
  }

  const raw = yaml.load(fs.readFileSync(filePath, "utf-8")) as Record<string, unknown>;
  if (!raw || typeof raw !== "object") {
    throw new Error("aeneas-config.yml is empty or invalid");
  }

  const config = raw as unknown as AeneasConfig;

  // Validate required fields
  if (!config.aeneas?.commit) throw new Error("Missing required field: aeneas.commit");
  if (!config.aeneas?.repo) throw new Error("Missing required field: aeneas.repo");

  return { config, root: projectRoot };
}
