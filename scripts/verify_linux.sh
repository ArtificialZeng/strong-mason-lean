#!/usr/bin/env bash
# Frozen Lean Eval comparator/nanoda replay. Run only against a complete package.
# Provenance: lean-eval@3f3786f3b4d9a4b64a5859b3036aca190cd25613
# .github/workflows/ci.yml, SECURITY.md, README.md. See notes/linux-verification.md.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: verify_linux.sh --submission-dir DIR --run-root NEW_DIR

DIR must contain a regular Submission.lean and, optionally, regular .lean
helpers under Submission/. Only those proof files are overlaid into a fresh
copy of the pinned official workspace. NEW_DIR must not exist and must be
outside DIR. The source package and this project's upstream/ are not changed.

Requires Linux with functioning Landlock, elan, Go 1.25.12, cargo, Python 3,
git, curl, a C compiler, make, tar, unzip, which and ldd. No hosted submission is made.
EOF
}

verification_submission_arg=
verification_root_arg=
while (($#)); do
  case "$1" in
    --submission-dir) (($# >= 2)) || { usage >&2; exit 2; }; verification_submission_arg=$2; shift 2 ;;
    --run-root) (($# >= 2)) || { usage >&2; exit 2; }; verification_root_arg=$2; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
[[ -n "$verification_submission_arg" && -n "$verification_root_arg" ]] || { usage >&2; exit 2; }
[[ $(uname -s) == Linux ]] || { printf '%s\n' 'This verifier requires Linux; no replay was attempted.' >&2; exit 2; }
for verification_cmd in git python3 go cargo rustc elan lake lean curl cc make tar unzip sha256sum tee which ldd; do
  command -v "$verification_cmd" >/dev/null || { printf 'Missing prerequisite: %s\n' "$verification_cmd" >&2; exit 2; }
done
[[ $(GOTOOLCHAIN=local go env GOVERSION) == go1.25.12 ]] || { printf '%s\n' 'Use the frozen CI Go version 1.25.12.' >&2; exit 2; }

# Do not let an ambient toolchain/import override replace the pinned Lake projects.
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT GOBIN
export GOTOOLCHAIN=local

verification_submission=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve(strict=True))' "$verification_submission_arg")
verification_root=$(python3 - "$verification_submission" "$verification_root_arg" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1])
target = Path(sys.argv[2]).resolve()
if target.exists() or target.is_symlink():
    raise SystemExit('Refusing to reuse an existing run root.')
if source == target or source in target.parents or target in source.parents:
    raise SystemExit('The run root and proof package must be separate.')
if not source.is_dir():
    raise SystemExit('The proof package must be a directory.')
target.mkdir(parents=True)
(target / 'logs').mkdir()
(target / 'metadata').mkdir()
print(target)
PY
)
verification_logs=$verification_root/logs
verification_meta=$verification_root/metadata
verification_phase=initializing
verification_passed=false
verification_finish() {
  local verification_exit=$?
  trap - EXIT
  python3 - "$verification_meta/result.json" "$verification_phase" "$verification_exit" "$verification_passed" <<'PY'
from pathlib import Path
import json, sys
passed = sys.argv[4] == 'true' and int(sys.argv[3]) == 0
Path(sys.argv[1]).write_text(json.dumps({
    'status': 'passed' if passed else 'failed',
    'last_phase': sys.argv[2], 'exit_code': int(sys.argv[3]),
    'scope': 'local frozen comparator plus nanoda replay; not a hosted receipt'
}, indent=2) + '\n')
PY
  exit "$verification_exit"
}
trap verification_finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

verification_stage() {
  local verification_name=$1
  shift
  verification_phase=$verification_name
  printf 'Verification stage: %s\n' "$verification_name"
  set +e
  "$@" 2>&1 | tee "$verification_logs/$verification_name.log"
  local verification_pipeline_status=("${PIPESTATUS[@]}")
  set -e
  local verification_status=${verification_pipeline_status[0]}
  if ((verification_status == 0 && verification_pipeline_status[1] != 0)); then
    verification_status=${verification_pipeline_status[1]}
  fi
  printf '%s\n' "$verification_status" >"$verification_logs/$verification_name.exit-code"
  return "$verification_status"
}

verification_benchmark_pin=3f3786f3b4d9a4b64a5859b3036aca190cd25613
verification_mathlib_pin=905b95818eb32af7874a58b427f50c1711a5e96c
verification_export_pin=4e7915201d3f9f04470d9eae002fa695f7cdc589
verification_comparator_pin=71b52ec29e06d4b7d882726553b1ceb99a2499e0
verification_nanoda_pin=68d5ca9db226849b41a6fff59d796ff19d0a8840
verification_landrun_pin=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
verification_toolchain=leanprover/lean4:v4.32.2
python3 - "$verification_meta/verifier-pins.json" "${BASH_SOURCE[0]}" <<'PY'
from pathlib import Path
import hashlib, json, sys
script = Path(sys.argv[2]).resolve()
Path(sys.argv[1]).write_text(json.dumps({
    'benchmark': '3f3786f3b4d9a4b64a5859b3036aca190cd25613',
    'mathlib': '905b95818eb32af7874a58b427f50c1711a5e96c',
    'landrun': '5ed4a3db3a4ad930d577215c6b9abaa19df7f99f',
    'lean4export': '4e7915201d3f9f04470d9eae002fa695f7cdc589',
    'comparator': '71b52ec29e06d4b7d882726553b1ceb99a2499e0',
    'nanoda': '68d5ca9db226849b41a6fff59d796ff19d0a8840',
    'workspace_toolchain': 'leanprover/lean4:v4.32.2',
    'comparator_toolchain': 'leanprover/lean4:v4.30.0-rc2',
    'go': '1.25.12', 'script_sha256': hashlib.sha256(script.read_bytes()).hexdigest()
}, indent=2) + '\n')
PY
verification_benchmark=$verification_root/benchmark
verification_tools=$verification_root/trusted-tools
verification_workspace=$verification_root/workspace
mkdir "$verification_tools"

verification_clone_pin() {
  local verification_url=$1 verification_pin=$2 verification_dir=$3
  git clone "$verification_url" "$verification_dir" || return $?
  git -C "$verification_dir" checkout --detach "$verification_pin" || return $?
  [[ $(git -C "$verification_dir" rev-parse HEAD) == "$verification_pin" ]]
}

verification_assert_lean_version() {
  local verification_expected=$1
  local verification_lean_version verification_lake_version
  verification_lean_version=$(lean --version) || return $?
  verification_lake_version=$(lake --version) || return $?
  printf '%s\n%s\n' "$verification_lean_version" "$verification_lake_version"
  if [[ "$verification_lean_version" != *"version $verification_expected,"* ||
        "$verification_lake_version" != *"(Lean version $verification_expected)"* ]]; then
    printf 'Expected actual Lean and Lake toolchain %s; ensure elan shims precede direct toolchain binaries on PATH.\n' "$verification_expected" >&2
    return 2
  fi
}

verification_build_lean_tool() {
  local verification_dir=$1 verification_expected=$2 verification_target=$3
  (
    cd "$verification_dir" || return $?
    verification_assert_lean_version "$verification_expected" || return $?
    lake build "$verification_target"
  )
}

verification_stage benchmark-checkout verification_clone_pin \
  https://github.com/leanprover/lean-eval.git "$verification_benchmark_pin" "$verification_benchmark"

# Validate the eight immutable trusted starter files, then copy proof sources
# as inert bytes. No source-package lakefile or .olean is ever used.
verification_stage stage-package python3 - "$verification_benchmark" "$verification_submission" "$verification_workspace" "$verification_meta" <<'PY'
from pathlib import Path
import hashlib, json, shutil, subprocess, sys
benchmark, source, target, metadata = map(Path, sys.argv[1:])
expected = {
 'ChallengeDeps.lean': 'cbfc7c6b62056ec20e8776689acf436ff613d3122e01a5c07aa9383972ba1fb1',
 'Challenge.lean': '034e9dd81cbd36ace08dc4430a4c571cd3ae31ce5bf77cf01d5aa19c35c8bfca',
 'Solution.lean': '6d9753e4fe7ba851b0deb946ab7cd571635155dd445f4f7bab76464374d896ea',
 'lean-toolchain': '2bdc48adfa58d0017e538a0ad117c5d73d35deec879978f909406a80c8037273',
 'lakefile.toml': '265c4966963b40a8691c772e28e663dd7698f4160050e28e2f3d4fc5d3103276',
 'config.json': '074811c075940ea89d0eee6a4c8604d225f89d76ed6ed4dc3d668bb3785079d0',
 'WorkspaceTest.lean': 'd550bdc174f54b363443785e203b3d84146b52434e80219640e15c8066806beb',
 'README.md': 'fd497abec7c5234609b61688779f8590a05dd47062303d921126ac143c8bfaaf'
}
starter = benchmark / 'generated/strong_mason_conjecture'
for name, digest in expected.items():
    if hashlib.sha256((starter / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Frozen trusted-file mismatch: {name}')
shutil.copytree(starter, target)
proof_files = [source / 'Submission.lean']
helpers = source / 'Submission'
if helpers.is_symlink():
    raise SystemExit('Submission/ must not be a symlink.')
if helpers.exists():
    if not helpers.is_dir():
        raise SystemExit('Submission/ must be a directory.')
    # Stronger than official skip-inside-symlink policy: reject all symlinks.
    for entry in helpers.rglob('*'):
        if entry.is_symlink():
            raise SystemExit(f'Proof-package symlink rejected: {entry}')
        if entry.is_file() and entry.suffix == '.lean':
            proof_files.append(entry)
rows = []
for path in sorted(proof_files):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f'Expected a regular proof file: {path}')
    rel = path.relative_to(source)
    destination = target / rel
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(path, destination)
    rows.append({'path': str(rel), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
for name, digest in expected.items():
    if hashlib.sha256((target / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Trusted file changed during overlay: {name}')
(metadata / 'trusted-files.json').write_text(json.dumps(expected, indent=2) + '\n')
(metadata / 'proof-files.json').write_text(json.dumps(rows, indent=2) + '\n')
try:
    source_commit = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True, stderr=subprocess.DEVNULL).strip()
except subprocess.CalledProcessError:
    source_commit = None
(metadata / 'source-snapshot.json').write_text(json.dumps({'source_directory': str(source), 'git_commit': source_commit, 'proof_files': rows}, indent=2) + '\n')
print(f'Staged {len(rows)} regular Lean proof files; eight trusted hashes unchanged.')
PY

verification_stage toolchain elan toolchain install "$verification_toolchain"
verification_stage landrun-install go install "github.com/zouuup/landrun/cmd/landrun@$verification_landrun_pin"
verification_stage exporter-checkout verification_clone_pin \
  https://github.com/leanprover/lean4export.git "$verification_export_pin" "$verification_tools/lean4export"
# This toolchain copy is the exact required frozen CI step: 4.32.0 exporter
# defaults cannot read 4.32.2 olean headers.
cp "$verification_benchmark/lean-toolchain" "$verification_tools/lean4export/lean-toolchain"
[[ $(cat "$verification_tools/lean4export/lean-toolchain") == "$verification_toolchain" ]]
verification_stage exporter-build verification_build_lean_tool "$verification_tools/lean4export" 4.32.2 lean4export
verification_stage comparator-checkout verification_clone_pin \
  https://github.com/leanprover/comparator.git "$verification_comparator_pin" "$verification_tools/comparator"
# Keep comparator's own pinned Lean 4.30.0-rc2 toolchain, as frozen CI does.
[[ $(cat "$verification_tools/comparator/lean-toolchain") == leanprover/lean4:v4.30.0-rc2 ]]
verification_stage comparator-build verification_build_lean_tool "$verification_tools/comparator" 4.30.0-rc2 comparator
verification_stage nanoda-checkout verification_clone_pin \
  https://github.com/robsimmons/nanoda_lib.git "$verification_nanoda_pin" "$verification_tools/nanoda"
verification_stage nanoda-build bash -euo pipefail -c 'cd "$1"; cargo build --release' _ "$verification_tools/nanoda"

export PATH="$verification_tools/comparator/.lake/build/bin:$verification_tools/lean4export/.lake/build/bin:$verification_tools/nanoda/target/release:$(go env GOPATH)/bin:$PATH"
export COMPARATOR_BIN="$verification_tools/comparator/.lake/build/bin/comparator"

verification_stage provenance bash -euo pipefail -c '
  uname -a
  if test -r /sys/kernel/security/lsm; then cat /sys/kernel/security/lsm; fi
  go version
  cargo --version
  rustc --version
  python3 --version
  elan --version
  cd "$1"
  lean --version
  lake --version
  for tool in comparator landrun lean4export nanoda_bin; do
    tool_path=$(command -v "$tool")
    printf "%s %s\n" "$tool" "$tool_path"
    sha256sum "$tool_path"
  done
  go version -m "$(command -v landrun)"
' _ "$verification_workspace"

verification_stage sandbox-engaged python3 "$verification_benchmark/scripts/sandbox_engaged_probe.py" --require-tools
verification_stage env-allowlist python3 "$verification_benchmark/scripts/security_probes/env_dump_probe.py" --require-tools
verification_stage benchmark-prime bash -euo pipefail -c 'cd "$1"; lake update; lake exe cache get' _ "$verification_benchmark"
verification_stage comparator-installation bash -euo pipefail -c 'cd "$1"; lake exe lean-eval check-comparator-installation' _ "$verification_benchmark"
verification_stage workspace-prime bash -euo pipefail -c 'cd "$1"; lake update; lake exe cache get' _ "$verification_workspace"
verification_stage dependency-pins python3 - "$verification_workspace" "$verification_mathlib_pin" "$verification_meta/dependency-pins.json" <<'PY'
from pathlib import Path
import json, subprocess, sys
workspace = Path(sys.argv[1])
manifest = json.loads((workspace / 'lake-manifest.json').read_text())
rows = []
for package in manifest['packages']:
    if package.get('type') != 'git':
        raise SystemExit(f'Unexpected non-git package: {package}')
    path = workspace / '.lake/packages' / package['name']
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit(f'Dependency checkout mismatch: {package["name"]}')
    rows.append({'name': package['name'], 'commit': actual})
if not any(p['name'] == 'mathlib' and p['commit'] == sys.argv[2] for p in rows):
    raise SystemExit('The frozen Mathlib pin is missing.')
Path(sys.argv[3]).write_text(json.dumps(rows, indent=2) + '\n')
print(f'Checked {len(rows)} dependency commits, including the exact frozen Mathlib.')
PY

# This is the acceptance command. Do not pre-build user Submission outside it.
# The unmodified WorkspaceTest dynamically forces enable_nanoda := true.
verification_stage lake-test bash -euo pipefail -c 'cd "$1"; lake test' _ "$verification_workspace"
verification_stage final-integrity python3 - "$verification_workspace" "$verification_meta" "$verification_logs/lake-test.log" <<'PY'
from pathlib import Path
import hashlib, json, sys
workspace, metadata, log = map(Path, sys.argv[1:])
expected = json.loads((metadata / 'trusted-files.json').read_text())
for name, digest in expected.items():
    if hashlib.sha256((workspace / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Trusted file changed: {name}')
for row in json.loads((metadata / 'proof-files.json').read_text()):
    if hashlib.sha256((workspace / row['path']).read_bytes()).hexdigest() != row['sha256']:
        raise SystemExit(f'Proof source changed during replay: {row["path"]}')
text = log.read_text(errors='replace')
for marker in ('Nanoda kernel accepts the solution', 'Lean default kernel accepts the solution', 'Your solution is okay!'):
    if marker not in text:
        raise SystemExit(f'Missing frozen comparator success marker: {marker}')
print('Exact lake test exited zero; nanoda and Lean replay markers present; source hashes unchanged.')
PY
verification_phase=complete
verification_passed=true
printf 'Frozen local comparator/nanoda replay passed. Evidence: %s\n' "$verification_root"
