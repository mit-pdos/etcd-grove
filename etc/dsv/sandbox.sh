#!/usr/bin/env bash
# The dsverify experiment's sandbox: a Claude Code agent proving a challenge exported by
# `etc/dsv/kitgen.py --export-challenge`, in a systemd-nspawn container of its own, with no view of
# the host's other files, no network except the Anthropic API, and only prefetched dependencies.
# (etc/dsv/README.md, "Running an experiment on a challenge".)
#
# The experiment directory DSV_LAB (required; outside the repository) holds the state:
#   mirrors/    read-only bare git mirrors (https://github.com/X/Y -> mirrors/github.com/X/Y.git)
#   cache/      the Go module cache (gomod-challenge), tools (claude, elan, the Lean toolchain, the
#               comparator's), the built Lake packages (lean/lakepkgs-<key>)
#   runs/RUN/   one run: its container root, home (the agent's only writable tree), its copy of the
#               experiment scripts it mounts (etc/dsv/), logs, meta.txt
#   token       the `claude setup-token` token (DSV_TOKEN names another file)
# IMAGE (required for new, start, start-shell): the root of the image whose /usr the containers
# mount read-only and whose /etc (without ssh, sudo or shadow files) each run copies.
#
# With network (preparing a challenge):
#   sandbox.sh mirror URL [BRANCH]   bare clone of a git repo (one branch if given) into mirrors/,
#                                    or fetch into it if it exists
#   sandbox.sh prefetch --challenge DIR  OFFLINE.txt's Go needs of the exported challenge DIR (every
#                                    module, Perennial's, every Go toolchain) into cache/gomod-challenge
#   sandbox.sh tools                 copy the claude binary, elan and the Lean toolchain into cache/tools
#                                    (CLAUDE_BIN, ELAN_HOME: where they are; default: claude on PATH,
#                                    ~/.elan)
# Offline:
#   sandbox.sh lakepkgs DIR          build the challenge's Lake packages from the mirrors into
#                                    cache/lean/lakepkgs-<key> (LAKE_WRAP: a command to run lake under)
# As root:
#   sandbox.sh new RUN               a fresh run without a challenge (the throwaway run test1, where the
#                                    generic check and verify run)
#   sandbox.sh new RUN --challenge DIR  a run of the exported challenge DIR (DIR.lab beside it)
#   sandbox.sh start RUN [ARGS...]   start Claude Code (ARGS passed on) in RUN's container
#   sandbox.sh start-shell RUN [CMD...] a shell (or CMD) in RUN's check view: the container, proxy
#                                    and all, with the check scripts mounted at /opt/lab
#   sandbox.sh set RUN KEY VALUE     a setting of RUN from now on, resumes included, in runs/RUN/config
#                                    (each change also logged in meta.txt); KEY is one of
#                                      cpus     the container's CPUs (start, start-shell), e.g. 0-15
#                                      memory   its memory cap, no swap (start, start-shell), e.g. 48G
#                                      model    the main session's model (start: claude --model), e.g.
#                                               opus; unset: opus
#                                      subagents the model of every subagent (model-hook.sh sets each
#                                               Agent call's model to it): opus, sonnet, haiku or
#                                               fable; unset: opus, whatever the main session's model
#                                      fable    the model the alias "fable" names, in the main session
#                                               and in subagents (ANTHROPIC_DEFAULT_FABLE_MODEL)
#                                      context  every session's context window, main and subagents
#                                               (CLAUDE_CODE_AUTO_COMPACT_WINDOW), 100k to 1M
#   sandbox.sh unset RUN KEY         remove a setting
#   sandbox.sh show RUN              RUN's settings and what start and start-shell add for them
#   sandbox.sh verify RUN TAG        rebuild the challenge run RUN's work tree at TAG from a fresh
#                                    checkout, in the throwaway run $VERIFY_RUN (test1): verify.sh;
#                                    log in runs/RUN/verify-TAG.log
#
# Inside: HOME=/home/agent (runs/RUN/home, the only writable tree), project dir /home/agent/work,
# CLAUDE_CONFIG_DIR=/home/agent/.claude (transcripts land in runs/RUN/home/.claude/projects).
# git URLs https://github.com/... resolve to mirrors/github.com/... (read-only); Go modules come
# from a download cache (GOPROXY=file://, no sum database); Lean from the toolchain in cache/tools.
# The only network is an HTTPS proxy (proxy.py, run on the host) that tunnels to api.anthropic.com
# and platform.claude.com and logs every request to runs/RUN/proxy.log.
#
# Auth: the token file (DSV_TOKEN, default $DSV_LAB/token: a `claude setup-token` token, mode 600),
# bound read-only at /run/lab-token (not on a command line, where ps shows it) and exported as
# CLAUDE_CODE_OAUTH_TOKEN by inside.sh. Never copy another config dir's credentials.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)            # etc/dsv: the experiment scripts
GROVE=$(cd "$HERE/../.." && pwd)               # the etcd-grove checkout
usage() { sed -n '2,63p' "$0" | sed -E 's/^# ?//'; exit 1; }
[ -n "${DSV_LAB:-}" ] || { [ -z "${1:-}" ] || [ "${1:-}" = --help ] || [ "${1:-}" = -h ] && usage
    echo "sandbox.sh: set DSV_LAB to the experiment directory (mirrors, caches, runs; outside the repository)" >&2; exit 1; }
LAB=$(cd "$DSV_LAB" && pwd)
# the commands that need root re-run themselves under sudo, keeping the settings
case "${1:-}" in new|start|start-shell|verify)
    [ "$(id -u)" = 0 ] || exec sudo --preserve-env=DSV_LAB,DSV_TOKEN,IMAGE,LEAN_TOOLCHAIN,VERIFY_RUN,SCRIPTS_OF "$0" "$@" ;;
esac
TOKEN=${DSV_TOKEN:-$LAB/token}
# the Lean toolchain of the runs, as cache/tools names it (default: etcd-grove's lean-toolchain)
LEAN_TOOLCHAIN=${LEAN_TOOLCHAIN:-$(sed 's#^leanprover/lean4:#leanprover--lean4---#' "$GROVE/lean-toolchain")}
IMAGE=${IMAGE:-}
export PATH=/usr/local/go/bin:$PATH

die() { echo "sandbox.sh: $*" >&2; exit 1; }
need_image() {
    [ -n "$IMAGE" ] || die "set IMAGE to the containers' image root (its /usr and /etc; etc/dsv/README.md)"
    [ -d "$IMAGE/usr/bin" ] || die "no $IMAGE/usr (IMAGE)"
}

# the experiment scripts a container mounts, copied into each run by `new` (runs/RUN/etc/dsv/): a
# live run is not changed by a change to the checkout (another branch checked out)
SNAPSHOT="proxy.py inside.sh ask-hook.sh model-hook.sh managed-settings.json check-env.sh verify.sh
          leak-names.txt statement/goal-check.sh statement/comparator-check.sh"
# the container's view: "SRC DST ro|rw" per line, SRC on the host's paths ($USR for /usr). The scripts
# are RUN's copy, or SCRIPTS_OF's (another run's: sandbox.sh verify and run.sh's generic check, in the
# throwaway run, use the checked run's)
mounts() {
    local R=$1 E=${SCRIPTS_OF:-$1}/etc/dsv
    [ -f "$E/inside.sh" ] || die "no $E (a run made before its scripts were copied in: make it again)"
    # the check scripts name what they look for: never in the agent's view
    if [ "${2:-}" = check ]; then
        echo "$E/check-env.sh /opt/lab/check-env.sh ro"
        echo "$E/verify.sh /opt/lab/verify.sh ro"
        echo "$E/statement/goal-check.sh /opt/lab/goal-check.sh ro"
        echo "$E/statement/comparator-check.sh /opt/lab/comparator-check.sh ro"
        # the names check-env.sh's leak check looks for (the `person` lines)
        echo "$E/leak-names.txt /opt/lab/leak-names.txt ro"
    fi
    # a challenge run's lab files (runs/RUN/goal: the export's DIR.lab, CHALLENGE.txt, the challenge
    # commit), for check-env.sh --challenge: check views only, never the agent's
    if [ "${2:-}" = check ] && [ -d "$R/goal/lab" ]; then echo "$R/goal /opt/lab/goal ro"; fi
    # the comparator, lean4export, landrun, nanoda (cache/tools/comparator: statement/comparator-tools.sh)
    if [ "${2:-}" = check ] && [ -d "$LAB/cache/tools/comparator/bin" ]; then
        echo "$LAB/cache/tools/comparator/bin /opt/lab/comparator/bin ro"
    fi
    # the Go module proxy: cache/gomod-challenge (sandbox.sh prefetch --challenge)
    local GOPROXY_DIR=$CHGOMOD/cache/download
    [ -d "$GOPROXY_DIR" ] || die "no $GOPROXY_DIR (sandbox.sh prefetch --challenge DIR)"
    cat <<EOF
$USR /usr ro
$R/home /home/agent rw
$R/sock /run/lab ro
$E/proxy.py /opt/lab/proxy.py ro
$E/inside.sh /opt/lab/inside.sh ro
$E/ask-hook.sh /opt/lab/ask-hook.sh ro
$E/model-hook.sh /opt/lab/model-hook.sh ro
$E/managed-settings.json /etc/claude-code/managed-settings.json ro
$LAB/mirrors /opt/mirrors ro
$GOPROXY_DIR /opt/goproxy ro
$LAB/cache/tools/claude /opt/claude/claude ro
$LAB/cache/tools/$LEAN_TOOLCHAIN /home/agent/.elan/toolchains/$LEAN_TOOLCHAIN ro
EOF
}

# the environment inside, "NAME=VALUE" per line
envs() {
    cat <<EOF
HOME=/home/agent
USER=agent
TERM=${TERM:-xterm-256color}
LANG=C.UTF-8
TMPDIR=/home/agent/tmp
PATH=/home/agent/.elan/bin:/home/agent/go/bin:/usr/local/go/bin:/opt/claude:/usr/local/bin:/usr/bin:/bin
ELAN_HOME=/home/agent/.elan
GOPATH=/home/agent/go
GOMODCACHE=/home/agent/go/pkg/mod
GOPROXY=file:///opt/goproxy
GOSUMDB=off
GOTOOLCHAIN=local
GOTELEMETRY=off
HTTPS_PROXY=http://127.0.0.1:3128
https_proxy=http://127.0.0.1:3128
NO_PROXY=localhost,127.0.0.1,::1
no_proxy=localhost,127.0.0.1,::1
CLAUDE_CONFIG_DIR=/home/agent/.claude
CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
DISABLE_AUTOUPDATER=1
ENABLE_CLAUDEAI_MCP_SERVERS=false
IS_SANDBOX=1
EOF
}

# runs/RUN/config: the run's settings, one KEY=VALUE per line. start and start-shell read it (never
# source it: it is data, and they run as root); set and unset write it and log each change in meta.txt.
CONFIG_KEYS="cpus memory model subagents fable context"
# config_value KEY VALUE: VALUE checked for KEY and printed as stored (context in tokens)
config_value() {
    local k=$1 v=$2 t
    case $k in
    cpus) [[ $v =~ ^[0-9]+(-[0-9]+)?(,[0-9]+(-[0-9]+)?)*$ ]] || die "cpus is a list like 0-15 or 0-7,16-23"
          echo "$v" ;;
    memory) [[ $v =~ ^[0-9]+[KMGT]$ ]] || die "memory is a size like 48G"
            echo "$v" ;;
    subagents) [[ $v =~ ^(opus|sonnet|haiku|fable)$ ]] || die "subagents is opus, sonnet, haiku or fable (the Agent tool's names)"
           echo "$v" ;;
    model) [[ $v =~ ^[a-z0-9.-]+$ ]] || die "model is a name like opus or claude-opus-5-5"
           echo "$v" ;;
    fable) [[ $v =~ ^claude-[a-z0-9.-]+$ ]] || die "fable is a model id like claude-fable-5-2"
           echo "$v" ;;
    context)
        if [[ $v =~ ^[0-9]+$ ]]; then t=$((10#$v))
        elif [[ $v =~ ^([0-9]+)[kK]$ ]]; then t=$((10#${BASH_REMATCH[1]} * 1000))
        elif [[ $v =~ ^([0-9]+)[mM]$ ]]; then t=$((10#${BASH_REMATCH[1]} * 1000000))
        else die "context is a token count like 100000 or 100k"; fi
        # Claude Code raises a window under 100k to 100k and lowers one over 1M to 1M, with only a
        # warning: refused here instead, so the recorded value is the one in force
        [ "$t" -ge 100000 ] && [ "$t" -le 1000000 ] || die "context must be 100k to 1M (Claude Code's range)"
        echo "$t" ;;
    *) die "unknown setting $k (one of: $CONFIG_KEYS)" ;;
    esac
}
# config_put RUN_DIR KEY [VALUE]: KEY's line replaced by KEY=VALUE, or removed without VALUE
config_put() {
    local R=$1 k=$2 v=${3:-} t="$1/config.tmp"
    {
        if [ -e "$R/config" ]; then grep -v "^$k=" "$R/config" || true; fi
        if [ -n "$v" ]; then echo "$k=$v"; fi
    } >"$t"
    if [ -s "$t" ]; then mv "$t" "$R/config"; else rm -f "$t" "$R/config"; fi
}
# config_read RUN_DIR: the settings into CFG, every line checked again (the file may be edited by hand)
declare -A CFG=()
config_read() {
    local R=$1 line k v
    CFG=()
    [ -e "$R/config" ] || return 0
    while IFS= read -r line || [ -n "$line" ]; do
        [ -n "$line" ] || continue
        [[ $line == *=* ]] || die "$R/config: not KEY=VALUE: $line"
        k=${line%%=*}
        v=$(config_value "$k" "${line#*=}") || die "$R/config: bad line: $line"
        CFG[$k]=$v
    done <"$R/config"
}
# config_apply start|start-shell: from CFG, the options for systemd-nspawn (NSPAWN_ARGS) and, for
# start, for claude (CLAUDE_ARGS). cpus and memory go on the container's scope; context is an
# environment variable inside, where every session (subagents run in the same process) reads it
config_apply() {
    NSPAWN_ARGS=(); CLAUDE_ARGS=()
    if [ -n "${CFG[cpus]:-}" ]; then NSPAWN_ARGS+=(--property="AllowedCPUs=${CFG[cpus]}"); fi
    if [ -n "${CFG[memory]:-}" ]; then
        NSPAWN_ARGS+=(--property="MemoryMax=${CFG[memory]}" --property="MemorySwapMax=0")
    fi
    [ "$1" = start ] || return 0
    if [ -n "${CFG[context]:-}" ]; then
        NSPAWN_ARGS+=(--setenv="CLAUDE_CODE_AUTO_COMPACT_WINDOW=${CFG[context]}")
    fi
    CLAUDE_ARGS+=(--model "${CFG[model]:-opus}") # opus unless the run names another
    # the alias for the main session (model=fable) and for the Agent tool's model "fable" alike
    if [ -n "${CFG[fable]:-}" ]; then NSPAWN_ARGS+=(--setenv="ANTHROPIC_DEFAULT_FABLE_MODEL=${CFG[fable]}"); fi
    # model-hook.sh puts every subagent on this model: opus unless the run's config names another
    NSPAWN_ARGS+=(--setenv="LAB_AGENT_MODEL=${CFG[subagents]:-opus}")
}

# Challenges: exported by `etc/dsv/kitgen.py --export-challenge DIR KIT`: DIR the tree the agent gets
# (CHALLENGE.txt, CLAUDE.md, the skill in .claude/skills/dsverify unless --no-skill), DIR.lab the
# lab's files (OFFLINE.txt, MANIFEST.txt, comparator/, kitlibs-check/), never in a run's view.
# Their Go modules come from cache/gomod-challenge (a module cache of its own: one file proxy serves
# one copy of each module version); their Lake packages, built, from cache/lean/lakepkgs-<key>/
# (`sandbox.sh lakepkgs DIR`).
CHGOMOD=$LAB/cache/gomod-challenge
# challenge_lab DIR: DIR.lab, checked
challenge_lab() {
    local d=$1
    [ -f "$d/CHALLENGE.txt" ] || die "$d: no CHALLENGE.txt (not an exported challenge)"
    [ -f "$d.lab/OFFLINE.txt" ] && [ -f "$d.lab/comparator/challenge.conf" ] ||
        die "no $d.lab/OFFLINE.txt or $d.lab/comparator/challenge.conf (kitgen writes them beside the export)"
    echo "$d.lab"
}
# lakepkgs_key DIR: the key of DIR's Lake packages (the manifest's packages and the toolchain)
lakepkgs_key() {
    python3 -I - "$1/lake-manifest.json" "$(cat "$1/lean-toolchain")" <<'EOF'
import hashlib, json, sys
m = json.load(open(sys.argv[1]))
s = sys.argv[2] + "\n" + "".join(f'{p["name"]} {p["url"]} {p["rev"]} {p.get("subDir")}\n'
                                 for p in sorted(m["packages"], key=lambda p: p["name"]))
print(hashlib.sha256(s.encode()).hexdigest()[:12])
EOF
}
# challenge_tc DIR: DIR's lean-toolchain, as cache/tools names it
challenge_tc() { sed 's#^leanprover/lean4:#leanprover--lean4---#' "$1/lean-toolchain"; }
# challenge_perennial_src DIR LABDIR DEST: Perennial at OFFLINE.txt's pin, from the mirror (its go.mod for goose)
challenge_perennial_src() {
    local pin; pin=$(sed -n 's/^perennial: \([0-9a-f]*\).*/\1/p' "$2/OFFLINE.txt")
    [ -n "$pin" ] || die "$2/OFFLINE.txt: no perennial:"
    git -C "$LAB/mirrors/github.com/mit-pdos/perennial.git" cat-file -e "$pin^{commit}" 2>/dev/null ||
        die "Perennial $pin is not in mirrors/ (fetch it: sandbox.sh mirror https://github.com/mit-pdos/perennial; tag the pin, refs/tags/lab-pin-<rev>, so that no later fetch loses it)"
    mkdir -p "$3"; git -C "$LAB/mirrors/github.com/mit-pdos/perennial.git" archive "$pin" | tar -x -C "$3"
}
# challenge_go TREE LABDIR MODE: OFFLINE.txt's Go needs. MODE fetch: download them into
# cache/gomod-challenge (network). MODE check: offline, through the file proxy a run gets (a scratch
# module cache), fail on anything missing. TREE: a copy of the challenge (`replace` directives name
# sibling directories, so each module is resolved in place); its go.mod and go.sum files may be
# rewritten (-mod=mod).
challenge_go() {
    local T=$1 L=$2 mode=$3 v d out miss bad=0 gobin=go img
    if [ -x "${SRC:-}/usr/local/go/bin/go" ]; then gobin=${SRC:-}/usr/local/go/bin/go; fi
    img=$("$gobin" version | awk '{print $3}')
    local MC; MC=$(mktemp -d "${TMPDIR:-/tmp}/chgo.XXXXXX")
    local envs=(GOFLAGS='-mod=mod -modcacherw' GOTOOLCHAIN=local GOWORK=off GOTELEMETRY=off)
    if [ "$mode" = fetch ]; then envs+=(GOMODCACHE="$CHGOMOD")
    else envs+=(GOMODCACHE="$MC/mod" GOPROXY="file://$CHGOMOD/cache/download" GOSUMDB=off); fi
    mkdir -p "$CHGOMOD"
    # the toolchains: the image's go, or golang.org/toolchain's module (GOTOOLCHAIN=goX fetches it from
    # the file proxy, with no sum database)
    for v in $(sed -n 's/^go-toolchain: \(go[0-9.]*\).*/\1/p' "$L/OFFLINE.txt" | sort -u); do
        local z=$CHGOMOD/cache/download/golang.org/toolchain/@v/v0.0.1-$v.linux-amd64.zip
        # (fetch: every toolchain, whatever this machine's go is: the image a run gets may differ)
        if [ "$mode" = check ] && [ "$v" = "$img" ]; then echo "  go toolchain $v: the image's"; continue; fi
        if [ "$mode" = fetch ] && [ ! -f "$z" ]; then
            (cd "$MC" && env "${envs[@]}" "$gobin" mod download golang.org/toolchain@v0.0.1-$v.linux-amd64) || bad=1
        fi
        if [ -f "$z" ]; then echo "  go toolchain $v: golang.org/toolchain@v0.0.1-$v.linux-amd64 (cache/gomod-challenge)"
        else echo "  MISSING go toolchain $v (sandbox.sh prefetch --challenge DIR)"; bad=1; fi
    done
    # the modules: OFFLINE.txt's, and Perennial's at the pin (goose and proofgen are built from it)
    challenge_perennial_src "$T" "$L" "$MC/perennial"
    while read -r d; do
        [ -n "$d" ] || continue
        # a module whose local `replace` names a directory the export left out cannot be resolved in
        # any run: noted, not required
        miss=$(cd "$d" && "$gobin" mod edit -json | python3 -I -c '
import json, os, sys
for r in json.load(sys.stdin).get("Replace") or []:
    p = r["New"]["Path"]
    if p.startswith((".", "/")) and not os.path.isfile(os.path.join(p, "go.mod")): print(p)')
        if [ -n "$miss" ]; then echo "  NOTE ${d#"$T"/}: skipped (its replace names $(echo $miss), not in the export)"; continue; fi
        if out=$(cd "$d" && env "${envs[@]}" "$gobin" mod download 2>&1); then :
        else echo "  MISSING the modules of ${d#"$T"/}: $(echo "$out" | grep -v '^go: downloading' | tail -2 | tr '\n' ' ')"; bad=1; fi
    done < <(sed -n 's/^go-module: //p' "$L/OFFLINE.txt" | sed "s#^#$T/#"; echo "$MC/perennial")
    # goose and proofgen, built as etc/goose.py builds them from the pinned Perennial: in Perennial's
    # own workspace (its go.work, whose other modules require further modules), which
    # `go mod download` in its root module alone does not fetch
    if out=$(cd "$MC/perennial" && env "${envs[@]}" GOWORK= GOFLAGS=-modcacherw "$gobin" build -o "$MC/bin/" ./goose/cmd/goose ./goose/cmd/proofgen 2>&1); then
        echo "  goose and proofgen build from Perennial at the pin"
    else echo "  MISSING goose's modules: $(echo "$out" | grep -v '^go: downloading' | tail -2 | tr '\n' ' ')"; bad=1; fi
    chmod -R u+w "$MC" 2>/dev/null; rm -rf "$MC"
    [ $bad = 0 ] && echo "  go modules: $(sed -n 's/^go-module: //p' "$L/OFFLINE.txt" | wc -l) of OFFLINE.txt and Perennial's, $([ "$mode" = fetch ] && echo fetched into || echo resolved offline from) cache/gomod-challenge"
    return $bad
}

cmd=${1:-}; shift || true
case "$cmd" in
mirror)
    url=${1:?usage: sandbox.sh mirror URL [BRANCH]}; branch=${2:-}
    rel=${url#https://}; rel=${rel%.git}
    dst="$LAB/mirrors/$rel.git"
    [ -e "$dst" ] && { git -C "$dst" fetch -q --prune origin; echo "updated $dst"; exit 0; }
    mkdir -p "$(dirname "$dst")"
    if [ -n "$branch" ]; then
        git clone -q --bare --single-branch --branch "$branch" "$url" "$dst"
    else
        git clone -q --bare "$url" "$dst"
    fi
    echo "mirrored $url${branch:+ ($branch)} -> $dst"
    ;;
prefetch)
    if [ "${1:-}" = --challenge ]; then
        D=$(cd "${2:?usage: sandbox.sh prefetch --challenge DIR}" && pwd); L=$(challenge_lab "$D")
        T=$(mktemp -d); trap 'chmod -R u+w "$T" 2>/dev/null; rm -rf "$T"' EXIT
        rsync -a --exclude=/.lake --exclude=/.git "$D/" "$T/"
        challenge_go "$T" "$L" fetch || die "prefetch incomplete"
        echo "prefetched $D's Go needs into $CHGOMOD"; exit 0
    fi
    die "usage: sandbox.sh prefetch --challenge DIR"
    ;;
tools)
    # the claude binary and the Lean toolchain the runs use, frozen: refresh them only between
    # experiments, never between the arms of one
    T="$LAB/cache/tools"; mkdir -p "$T"
    cb=${CLAUDE_BIN:-$(command -v claude || true)}; [ -n "$cb" ] || die "no claude on PATH (CLAUDE_BIN)"
    eh=${ELAN_HOME:-$HOME/.elan}; [ -x "$eh/bin/elan" ] || die "no $eh/bin/elan (ELAN_HOME)"
    [ -d "$eh/toolchains/$LEAN_TOOLCHAIN" ] || die "no $eh/toolchains/$LEAN_TOOLCHAIN (elan toolchain install $(cat "$GROVE/lean-toolchain"))"
    cp "$(readlink -f "$cb")" "$T/claude"
    cp "$eh/bin/elan" "$T/elan"
    [ -d "$T/$LEAN_TOOLCHAIN" ] || cp -a "$eh/toolchains/$LEAN_TOOLCHAIN" "$T/"
    "$T/claude" --version
    ;;
lakepkgs)
    # lakepkgs DIR: the Lake packages of the exported challenge DIR (its lake-manifest.json: Perennial
    # and its dependencies), cloned from the mirrors at the manifest's pins and built with the runs'
    # toolchain, offline, as a run would: every module of theirs the challenge's Lean imports. Into
    # cache/lean/lakepkgs-<key>/packages (key: the packages' revisions and the toolchain; KEY lists
    # them), read-only; `new --challenge` copies it into the run's work tree. LAKE_WRAP: a command to
    # run the build under (e.g. one that limits concurrent builds).
    D=$(cd "${1:?usage: sandbox.sh lakepkgs DIR}" && pwd); L=$(challenge_lab "$D")
    TC=$(challenge_tc "$D"); TB="$LAB/cache/tools/$TC/bin"
    [ -x "$TB/lake" ] || die "no toolchain cache/tools/$TC (sandbox.sh tools)"
    key=$(lakepkgs_key "$D"); C="$LAB/cache/lean"; name=lakepkgs-$key
    if [ -d "$C/$name" ]; then echo "lakepkgs: $C/$name exists"; exit 0; fi
    mkdir -p "$C"; W=$(mktemp -d "$C/.tmp-lakepkgs-XXXXXX")
    trap 'chmod -R u+w "$W" 2>/dev/null; rm -rf "$W"' EXIT
    cat >"$W/gitconfig" <<EOF
[url "file://$LAB/mirrors/github.com/"]
	insteadOf = https://github.com/
[safe]
	directory = *
[advice]
	detachedHead = false
EOF
    export GIT_CONFIG_GLOBAL=$W/gitconfig GIT_CONFIG_NOSYSTEM=1 PATH=$TB:$PATH HOME=$W/home
    unset ELAN_HOME LEAN_PATH LEAN_SRC_PATH
    # the challenge's lakefile and manifest, and its Lean sources (for the imports)
    rsync -a --exclude=/.lake --exclude=/.git --exclude=/.claude "$D/" "$W/tree/"
    # the packages, at the manifest's pins (lake materializes them from the manifest, offline)
    (cd "$W/tree" && lake env true) >"$W/resolve.log" 2>&1 || { tail -5 "$W/resolve.log"; die "lake could not set up the packages from the mirrors"; }
    python3 -I - "$W/tree/lake-manifest.json" "$W/tree/.lake/packages" <<'EOF' || die "a package is not at its pin"
import json, subprocess, sys
for p in json.load(open(sys.argv[1]))["packages"]:
    d = f'{sys.argv[2]}/{p["name"]}'
    h = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    u = subprocess.run(["git", "-C", d, "config", "--get", "remote.origin.url"], capture_output=True, text=True).stdout.strip()
    print(f'  {p["name"]} {h[:12]} {u}')
    if h != p["rev"] or u != p["url"]: sys.exit(1)
EOF
    # the targets: every package module some module of the tree imports
    mods=$(python3 -I - "$W/tree" <<'EOF'
import os, re, sys
T = sys.argv[1]; P = os.path.join(T, ".lake/packages")
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
pkgmods = set()
for dp, ds, fs in os.walk(T):
    ds[:] = [d for d in ds if d not in (".lake", ".git", ".claude")]
    for f in fs:
        if f.endswith(".lean"):
            for i in IMP.findall(open(os.path.join(dp, f), errors="replace").read()):
                top = i.split(".")[0]
                if top in ("Perennial", "Iris", "Batteries", "Qq") and not os.path.exists(os.path.join(T, i.replace(".", "/") + ".lean")):
                    pkgmods.add(i)
# only modules that exist in a package (an import of a module the export left out is not built)
def exists(m):
    rel = m.replace(".", "/") + ".lean"
    for pk in os.listdir(P):
        for sub in ("", "Iris"):   # iris-lean: the package is its subdirectory Iris (the manifest: subDir)
            if os.path.exists(os.path.join(P, pk, sub, rel)):
                return True
    return False
print("\n".join(sorted(m for m in pkgmods if exists(m))))
EOF
)
    [ -n "$mods" ] || die "no package modules found to build"
    echo "lakepkgs: building $(echo "$mods" | wc -l) package modules the challenge imports (with their dependencies)"
    start=$(date +%s)
    # shellcheck disable=SC2086
    (cd "$W/tree" && ${LAKE_WRAP:-} lake build $mods) >"$W/build.log" 2>&1 || { cp "$W/build.log" "$C/lakepkgs-failed.log"; grep -E 'error' "$W/build.log" | head -10; die "lake build failed (log: $C/lakepkgs-failed.log)"; }
    tail -1 "$W/build.log"
    echo "lakepkgs: built in $(( $(date +%s) - start )) s"
    mkdir -p "$W/out"; mv "$W/tree/.lake/packages" "$W/out/packages"
    {
        echo "toolchain: $TC ($("$TB/lean" --version))"
        python3 -I -c 'import json, sys
for p in json.load(open(sys.argv[1]))["packages"]: print("package:", p["name"], p["url"], p["rev"])' "$D/lake-manifest.json"
        echo "built-for: $(sed -n 's/^source: //p' "$D/CHALLENGE.txt") ($(echo "$mods" | wc -l) imported package modules)"
        echo "built: $(date -Is)"
    } >"$W/out/KEY"
    mv "$W/out" "$C/$name"; chmod -R a-w "$C/$name"
    echo "lakepkgs: $C/$name"; cat "$C/$name/KEY"
    ;;
new)
    run=${1:?usage: sandbox.sh new RUN [--challenge DIR]}
    [ "$(id -u)" = 0 ] || die "run this as root (it reads IMAGE and hands the run to DSV_LAB's owner)"
    need_image; SRC=$IMAGE
    R="$LAB/runs/$run"; [ -e "$R" ] && die "$R exists"
    [ -x "$LAB/cache/tools/claude" ] || die "no cache/tools (sandbox.sh tools)"
    [ -d "$LAB/cache/tools/$LEAN_TOOLCHAIN" ] || die "no cache/tools/$LEAN_TOOLCHAIN (sandbox.sh tools)"
    [ -d "$CHGOMOD/cache/download" ] || die "no cache/gomod-challenge (sandbox.sh prefetch --challenge DIR)"
    # a challenge exported from etcd-grove
    CH=; CHL=
    if [ -n "${2:-}" ]; then
        [ "$2" = --challenge ] || die "usage: sandbox.sh new RUN [--challenge DIR]"
        CH=$(cd "${3:?usage: sandbox.sh new RUN --challenge DIR}" && pwd) || die "no $3"; CHL=$(challenge_lab "$CH")
        [ "$(challenge_tc "$CH")" = "$LEAN_TOOLCHAIN" ] || die "the challenge wants $(cat "$CH/lean-toolchain"), the runs' toolchain is $LEAN_TOOLCHAIN"
        LP="$LAB/cache/lean/lakepkgs-$(lakepkgs_key "$CH")"
        [ -f "$LP/KEY" ] || die "no built Lake packages for this challenge ($LP): sandbox.sh lakepkgs $CH"
    fi
    # as root, git refuses repos owned by someone else; the files are handed to $LAB's owner at the end
    git() { command git -c safe.directory='*' "$@"; }
    mkdir -p "$R"/home/{work,tmp,.claude,.elan/bin,.elan/toolchains/$LEAN_TOOLCHAIN,go} "$R/sock"
    # the experiment scripts the container mounts, as of now (meta.txt: the commit they come from)
    for f in $SNAPSHOT; do install -D -m "$([ -x "$HERE/$f" ] && echo 555 || echo 444)" "$HERE/$f" "$R/etc/dsv/$f"; done
    # the container's root: an empty /usr to mount on, and a copy of /etc without secrets
    mkdir -p "$R/root"/{usr,home/agent,opt,run,tmp,proc,sys,dev,var/tmp}
    for l in bin lib lib64 sbin; do ln -s "usr/$l" "$R/root/$l"; done
    tar -C "$SRC" --exclude=etc/{ssh,sudoers,sudoers.d,shadow,shadow-,gshadow,gshadow-,machine-id,hostname,chrony} \
        -cf - etc 2>/dev/null | tar -C "$R/root" -x --no-same-owner
    : >"$R/root/etc/machine-id"
    echo lab >"$R/root/etc/hostname"
    printf '127.0.0.1 localhost lab\n::1 localhost\n' >"$R/root/etc/hosts"
    H="$R/home"
    cp "$LAB/cache/tools/elan" "$H/.elan/bin/elan"
    for t in lean lake leanc leanmake lean-language-server; do ln -s elan "$H/.elan/bin/$t"; done
    printf 'telemetry = false\nversion = "12"\ndefault_toolchain = "%s"\n\n[overrides]\n' \
        "$LEAN_TOOLCHAIN" >"$H/.elan/settings.toml"
    cat >"$H/.gitconfig" <<'EOF'
[user]
	name = dsverify agent
	email = agent@localhost
[url "file:///opt/mirrors/github.com/"]
	insteadOf = https://github.com/
[init]
	defaultBranch = main
[safe]
	directory = *
EOF
    # additionalDirectories: the skill's files are readable without a permission prompt
    cat >"$H/.claude/settings.json" <<'EOF'
{
  "permissions": {
    "deny": ["WebFetch", "WebSearch", "RemoteTrigger"],
    "additionalDirectories": ["/home/agent/.claude/skills"]
  },
  "includeCoAuthoredBy": false,
  "autoUpdates": false
}
EOF
    # without this, a fresh config dir runs first-run onboarding (theme, then a login screen that
    # ignores CLAUDE_CODE_OAUTH_TOKEN) and asks to trust the workdir
    cat >"$H/.claude/.claude.json" <<'EOF'
{
  "hasCompletedOnboarding": true,
  "theme": "dark",
  "projects": {
    "/home/agent/work": { "hasTrustDialogAccepted": true }
  }
}
EOF
    chskill=; chcommit=
    if [ -n "$CH" ]; then
        # a half-made challenge run is removed: nothing of it is usable
        trap '[ $? = 0 ] || { echo "sandbox.sh: removing the half-made $R" >&2; chmod -R u+w "$R" 2>/dev/null; rm -rf "$R"; }' EXIT
        W="$H/work"
        # the work tree: the exported tree as it is (no .git, no .lake), a fresh repository below
        rsync -a --exclude=/.git --exclude=/.lake "$CH/" "$W/"
        # its Go needs, offline, through the file proxy the run gets (the check may rewrite go.mod and
        # go.sum files: they are copied back from the export afterwards)
        echo "checking the challenge's Go needs offline (OFFLINE.txt; a few minutes)"
        challenge_go "$W" "$CHL" check || die "the challenge's Go needs are not all in cache/gomod-challenge (sandbox.sh prefetch --challenge $CH)"
        (cd "$CH" && find . -path ./.lake -prune -o \( -name go.mod -o -name go.sum \) -print0) |
            (cd "$CH" && xargs -0 -r cp --parents -t "$W")
        # the skill: the challenge's .claude/skills/dsverify becomes the run's skill (in the config dir);
        # nothing else of .claude may be in an export
        chskill=$(sed -n 's/^skill: \([0-9a-f]*\).*/\1/p' "$W/CHALLENGE.txt")
        if [ -d "$W/.claude" ]; then
            other=$(cd "$W/.claude" && find . -mindepth 1 -maxdepth 2 ! -path ./skills ! -path ./skills/dsverify)
            [ -z "$other" ] || die "the export's .claude holds more than the skill: $other"
            if [ -d "$W/.claude/skills/dsverify" ]; then
                [ -n "$chskill" ] || die "the export has a skill, but CHALLENGE.txt names none"
                # its tree hash, as etcd-grove's `git rev-parse REV:.claude/skills/dsverify` gives it
                t=$(mktemp -d); git init -q --bare "$t/g"
                got=$(cd "$W/.claude/skills/dsverify" && GIT_DIR="$t/g" GIT_INDEX_FILE="$t/index" GIT_WORK_TREE=. \
                    sh -c 'git add -A && git write-tree')
                rm -rf "$t"
                [ "$got" = "$chskill" ] || die "the export's skill has tree $got; CHALLENGE.txt says $chskill"
                mkdir -p "$H/.claude/skills"; mv "$W/.claude/skills/dsverify" "$H/.claude/skills/dsverify"
            fi
            rm -rf "$W/.claude"
        elif [ -n "$chskill" ]; then die "CHALLENGE.txt names skill $chskill, but the export has no .claude/skills/dsverify"
        fi
        # the Lake packages, built (a copy: the agent's builds write into them)
        mkdir -p "$W/.lake"; cp -a "$LP/packages" "$W/.lake/packages"; chmod -R u+w "$W/.lake/packages"
        # the repository: one commit, the challenge as exported (its hash, recorded outside the agent's
        # view, names the pristine tree in every later check)
        git -C "$W" init -q
        git -C "$W" add -A
        git -C "$W" -c user.name="dsverify lab" -c user.email=lab@localhost \
            commit -q -m "challenge: $(sed -n 's/^kit: //p' "$W/CHALLENGE.txt") from etcd-grove $(sed -n 's/^source: //p' "$W/CHALLENGE.txt")"
        git -C "$W" tag challenge
        chcommit=$(git -C "$W" rev-parse HEAD)
        [ -z "$(git -C "$W" status --porcelain)" ] || die "the work tree is not clean after the initial commit"
        # the lab's side (never in the agent's view): DIR.lab, CHALLENGE.txt, the initial commit
        mkdir -p "$R/goal"; cp -a "$CHL" "$R/goal/lab"; cp "$W/CHALLENGE.txt" "$R/goal/CHALLENGE.txt"
        printf 'commit=%s\nsource=%s\nlakepkgs=%s\n' "$chcommit" "$CH" "$(basename "$LP")" >"$R/goal/challenge"
    fi
    {
        echo "run: $run"
        echo "created: $(date -Is)"
        echo "scripts: etcd-grove $(git -C "$GROVE" rev-parse HEAD 2>/dev/null || echo '?')$([ -n "$(git -C "$GROVE" status --porcelain -- etc/dsv 2>/dev/null)" ] && echo ' with uncommitted changes in etc/dsv') ($HERE, copied into runs/$run/etc/dsv)"
        if [ -n "$CH" ]; then
            echo "challenge: $CH (commit $chcommit in the work tree, tag challenge)"
            sed 's/^/  /' "$R/goal/CHALLENGE.txt"
            echo "challenge-lab: $CHL"
            (cd "$CHL" && find . -type f | LC_ALL=C sort | xargs sha256sum | sed 's/^/  /')
            echo "skill: ${chskill:-none}${chskill:+ (tree $chskill: the .claude/skills/dsverify of the challenge)}"
            echo "lakepkgs: $(basename "$LP")"; sed 's/^/  /' "$LP/KEY"
            echo "gomod: cache/gomod-challenge"
        else
            echo "skill: none"
        fi
        echo "claude: $("$LAB/cache/tools/claude" --version)"
        echo "lean: $LEAN_TOOLCHAIN"
        echo "go: $("$SRC/usr/local/go/bin/go" version)"
        echo "mirrors:"; (cd "$LAB/mirrors" && for m in $(find . -name '*.git' -type d -prune | sort); do
            echo "  $m $(git -C "$m" rev-parse HEAD)"; done)
    } >"$R/meta.txt"
    chown -R --reference="$LAB" "$R"
    echo "created $R"; cat "$R/meta.txt"
    ;;
start|start-shell)
    run=${1:?usage: sandbox.sh $cmd RUN ...}; shift
    R="$LAB/runs/$run"; [ -d "$R" ] || die "no run $run"
    [ "$(id -u)" = 0 ] || die "run this as root"
    command -v systemd-nspawn >/dev/null || die "no systemd-nspawn here"
    need_image; USR="$IMAGE/usr"
    # the run's settings (sandbox.sh set), checked before anything starts
    config_read "$R"; config_apply "$cmd"
    # a container killed uncleanly leaves its unix-export mount point behind, and nspawn then refuses
    X="/run/systemd/nspawn/unix-export/dsverify-$run"
    if [ -e "$X" ]; then
        pgrep -f -- "--machine=dsverify-$run( |$)" >/dev/null && die "dsverify-$run is already running"
        mountpoint -q "$X" && umount "$X"
        rmdir "$X" && echo "removed stale $X"
    fi
    rm -f "$R/sock/proxy.sock"
    [ -f "$R/etc/dsv/proxy.py" ] || die "no $R/etc/dsv (a run made before its scripts were copied in: make it again)"
    python3 "$R/etc/dsv/proxy.py" serve "$R/sock/proxy.sock" "$R/proxy.log" &
    PROXY=$!
    trap 'kill $PROXY 2>/dev/null' EXIT
    for _ in $(seq 50); do [ -S "$R/sock/proxy.sock" ] && break; sleep 0.1; done
    [ -S "$R/sock/proxy.sock" ] || die "proxy did not start"
    args=(--quiet --directory="$R/root" --machine="dsverify-$run" --as-pid2 --private-network
          --private-users=pick --private-users-ownership=auto --resolv-conf=off --timezone=off
          --link-journal=no --register=no --console=interactive --chdir=/home/agent/work)
    # the settings' options (config_apply): the scope's CPUs and memory; for start, the context window
    args+=("${NSPAWN_ARGS[@]}")
    if [ -e "$R/config" ]; then echo "config: $(tr '\n' ' ' <"$R/config")"; fi
    while read -r src dst mode; do
        if [ "$mode" = rw ]; then args+=(--bind="$src:$dst:idmap"); else args+=(--bind-ro="$src:$dst:idmap"); fi
    done < <(mounts "$R" "$([ "$cmd" = start-shell ] && echo check)")
    # verify: the checkout is the work tree
    if [ "$cmd" = start-shell ] && [ -n "${WORK_BIND:-}" ]; then args+=(--bind="$WORK_BIND:/home/agent/work:idmap"); fi
    while read -r e; do args+=(--setenv="$e"); done < <(envs)
    if [ "$cmd" = start ]; then
        [ -r "$TOKEN" ] || die "no token file $TOKEN (claude setup-token; DSV_TOKEN)"
        # bound in, not --setenv: a command line is visible to every user on the host (ps);
        # inside.sh reads it into CLAUDE_CODE_OAUTH_TOKEN
        args+=(--bind-ro="$TOKEN:/run/lab-token:idmap")
        # claude's options from the settings (the model), after "$@" like inside.sh's own options
        set -- "$@" "${CLAUDE_ARGS[@]}"
        systemd-nspawn "${args[@]}" /bin/bash /opt/lab/inside.sh claude "$@"
    else
        [ $# -gt 0 ] || set -- bash -i
        systemd-nspawn "${args[@]}" /bin/bash /opt/lab/inside.sh "$@"
    fi
    ;;
set)
    # cpus: a cpuset (the container sees only these: nproc, lake's parallelism); memory: a hard cap
    # (the kernel reclaims, then kills inside the container), with no swap, so a cap is a cap
    run=${1:?usage: sandbox.sh set RUN KEY VALUE}; R="$LAB/runs/$run"; [ -d "$R" ] || die "no run $run"
    k=${2:?usage: sandbox.sh set RUN KEY VALUE}; v=${3:?usage: sandbox.sh set RUN KEY VALUE}
    v=$(config_value "$k" "$v") || exit 1
    config_put "$R" "$k" "$v"
    echo "config: $k=$v ($(date -u +%FT%TZ))" >>"$R/meta.txt"
    echo "$run: $k=$v"
    ;;
unset)
    run=${1:?usage: sandbox.sh unset RUN KEY}; R="$LAB/runs/$run"; [ -d "$R" ] || die "no run $run"
    k=${2:?usage: sandbox.sh unset RUN KEY}
    case " $CONFIG_KEYS " in *" $k "*) ;; *) die "unknown setting $k (one of: $CONFIG_KEYS)" ;; esac
    config_put "$R" "$k"
    echo "config: $k unset ($(date -u +%FT%TZ))" >>"$R/meta.txt"
    echo "$run: $k unset"
    ;;
show)
    run=${1:?usage: sandbox.sh show RUN}; R="$LAB/runs/$run"; [ -d "$R" ] || die "no run $run"
    config_read "$R"
    for k in $CONFIG_KEYS; do echo "$k: ${CFG[$k]:-(unset)}"; done
    config_apply start; echo "start adds:       ${NSPAWN_ARGS[*]:-} ${CLAUDE_ARGS[*]:+(claude) ${CLAUDE_ARGS[*]}}"
    config_apply start-shell; echo "start-shell adds: ${NSPAWN_ARGS[*]:-}"
    ;;
verify)
    run=${1:?usage: sandbox.sh verify RUN TAG}; tag=${2:?usage: sandbox.sh verify RUN TAG}
    [ "$(id -u)" = 0 ] || die "run this as root"
    R="$LAB/runs/$run"; [ -d "$R" ] || die "no run $run"
    [ -f "$R/goal/challenge" ] || die "$run is not a challenge run (sandbox.sh new RUN --challenge DIR)"
    V=${VERIFY_RUN:-test1}; [ -d "$LAB/runs/$V" ] || die "no run $V (verify works in a throwaway run: sandbox.sh new $V)"
    [ "$V" != "$run" ] || die "verify works in a run other than $run (VERIFY_RUN)"
    # one container per run: a second verify (another arm finishing) waits for the first
    exec 9>"$LAB/runs/$V/.verify.lock"; flock 9
    git() { command git -c safe.directory='*' "$@"; }
    W="$R/home/work"
    # the project is the work tree itself (the challenge's repository), checked out at TAG as the check
    # view's work tree, with the built Lake packages (not the run's) and the lab's files beside it
    # (.goal); its Go modules from the run's module cache
    git -C "$W" rev-parse -q --verify "refs/tags/$tag" >/dev/null || die "no tag $tag in $W"
    D="$LAB/runs/$V/home/work/verify-$run"; rm -rf "$D"
    trap 'chmod -R u+w "$D" 2>/dev/null; rm -rf "$D"' EXIT
    git clone -q --no-local --no-checkout "$W" "$D"
    git -C "$D" -c advice.detachedHead=false checkout -q "$tag"
    LP="$LAB/cache/lean/$(sed -n 's/^lakepkgs=//p' "$R/goal/challenge")"; [ -f "$LP/KEY" ] || die "no $LP"
    mkdir -p "$D/.lake"; cp -a "$LP/packages" "$D/.lake/packages"; chmod -R u+w "$D/.lake/packages"
    cp -r "$R/goal" "$D/.goal"
    log="$R/verify-${tag//\//_}.log"; rc=0
    SCRIPTS_OF="$R" WORK_BIND="$D" "$0" start-shell "$V" bash /opt/lab/verify.sh /home/agent/work 2>&1 |
        grep --line-buffered -v '^go: downloading' | tee "$log" || rc=$?
    echo "log: $log (checkout removed)"
    exit $rc
    ;;
-h|--help|"") usage ;;
*) echo "sandbox.sh: unknown command $cmd" >&2; usage ;;
esac
