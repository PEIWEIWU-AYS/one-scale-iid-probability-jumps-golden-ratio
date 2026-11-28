"""Rebuild the endpoint proofs one module at a time, then audit their axioms."""

import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OWNERS = (
    ROOT,
    ROOT / ".lake/packages/iid_infinite_jumps",
    ROOT / ".lake/packages/iid_jump_spectra",
)
THEOREMS = (
    "MultinacciBands.population_endpoint_limit",
    "MultinacciBands.unrestricted_upper",
    "FullRankWindow.positive_logarithmic_population_correction",
    "FullRankWindow.threshold_witness_log_excess",
    "FullRankWindow.threshold_beats_fixed_ceilings",
    "MultinacciBands.explicit_right_interval_strict_cap",
    "MultinacciBands.logarithmic_run_strict_cap",
    "MultinacciBands.band_reach_upper",
    "MultinacciBands.square_root_band_reach",
    "MultinacciBands.optimal_band_reach",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^import\s+([\w.]+)\s*$", re.MULTILINE)
AUDIT = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)


def proof_order():
    """Local research modules in dependency order, including the two pinned papers."""
    modules = {}

    def visit(name):
        if name in modules or name.split(".")[0] in {"Mathlib", "Lean", "Std", "Init"}:
            return
        source = Path(*name.split(".")).with_suffix(".lean")
        owner = next((d for d in OWNERS if (d / source).is_file()), None)
        if owner is None:
            raise SystemExit(f"Missing dependency source: {name}. Run lake update.")
        for dependency in IMPORT.findall((owner / source).read_text(encoding="utf-8")):
            visit(dependency)
        modules[name] = (owner, source)

    visit("EndpointAsymptotics")
    return modules


def main():
    if "LEAN_PATH" not in os.environ:
        raise SystemExit("Run from the repository root: lake env python3 tools/verify.py")
    paths = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    print(version, flush=True)
    modules = proof_order()
    with tempfile.TemporaryDirectory(prefix="iid-endpoint-") as directory:
        build = Path(directory)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([directory, *paths]))
        for name, (owner, source) in modules.items():
            target = (build / source).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run = subprocess.run(
                ["lean", "-j1", "-DwarningAsError=true", "-o", str(target), str(source)],
                cwd=owner, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if run.returncode:
                raise SystemExit(f"Verification failed in {name}\n{run.stdout}")
            for theorem, axioms in AUDIT.findall(run.stdout):
                unexpected = set(axioms.split(", ")) - STANDARD_AXIOMS
                if unexpected:
                    raise SystemExit(f"Unexpected axioms for {theorem}: {unexpected}")
            if name == "EndpointAsymptotics":
                names = [theorem for theorem, _ in AUDIT.findall(run.stdout)]
                if names != list(THEOREMS):
                    raise SystemExit(f"Incomplete endpoint axiom audit:\n{run.stdout}")
                print(run.stdout.strip())
    print(f"Rebuilt {len(modules)} research modules sequentially.")


if __name__ == "__main__":
    main()
