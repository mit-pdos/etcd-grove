#!/usr/bin/env python3
# Usage: etc/dsv/rundone.py [--idle MIN] [--goal-idle MIN] [--sample SEC] [--scope DIR] RUN (as root; RUN
# as for tokens.py): whether a run's agent is done, from what the lab sees of it (experiment.sh wait and
# done; they also read Claude Code's screen, which this does not). Prints one line, DONE or NOT DONE with
# why, and exits 0 when done, 1 when not. Read-only: it changes nothing in the run.
#
# Never done while a Lean, Lake, Go or test process in the run's container uses the CPU (over SEC
# seconds, default 10: an idle Lean server, such as the ones a lean-check keeps for an hour, does not
# count). Then done when either
#   goal   the goal looks proved: on the branch `finish` would tag (the tag `final`, else the newest
#          branch) every stub of the challenge (CHALLENGE.txt's `omitted:` files that had a `sorry`) has
#          none, nor has any Lean file the branch changed since the challenge commit (comments left out);
#          the work tree has no uncommitted change to a tracked file; and no transcript (the session's,
#          its subagents') has grown for --goal-idle minutes (default 10). It does not build or verify:
#          that is `finish`'s verify;
#   idle   no session or subagent has made a tool call for --idle minutes (default 20; turns that only
#          talk or schedule, a wakeup finding nothing to do, are not work).
import argparse, datetime, glob, json, os, re, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokens
from backtrack import strip

BUSY = re.compile(r'^(lean|lake|go|compile|link|asm|.*\.test)$')
NOOP = {'ScheduleWakeup', 'CronCreate', 'CronDelete', 'CronList'}


def procs(scope):
    """{pid: (comm, cpu ticks)} of the Lean, Lake, Go and test processes in the cgroup tree `scope`"""
    out = {}
    for root, _, files in os.walk(scope):
        if 'cgroup.procs' not in files: continue
        try: pids = open(os.path.join(root, 'cgroup.procs')).read().split()
        except OSError: continue
        for pid in pids:
            try:
                st = open('/proc/%s/stat' % pid).read()
                comm = st[st.index('(') + 1:st.rindex(')')]; f = st[st.rindex(')') + 2:].split()
            except (OSError, ValueError): continue
            if BUSY.match(comm): out[pid] = (comm, int(f[11]) + int(f[12]))
    return out


def busy(scope, sample):
    """the processes that used the CPU during `sample` seconds: [(comm, seconds)]"""
    a = procs(scope)
    if not a: return []
    time.sleep(sample); b = procs(scope); hz = os.sysconf('SC_CLK_TCK')
    used = [(c, (t - a.get(p, (c, 0))[1]) / hz) for p, (c, t) in b.items()]
    return [(c, s) for c, s in used if s >= 0.01 * sample]   # 1% of a core


def last_growth(run):
    """minutes since a transcript last grew"""
    ts = [os.path.getmtime(f) for f, _ in tokens.transcripts(run)]
    return (time.time() - max(ts)) / 60 if ts else None


def worked_within(run, minutes):
    """some session or subagent made a tool call (but a scheduling one) in the last `minutes`"""
    cut = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(minutes=minutes)
    for f, _ in tokens.transcripts(run):
        if os.path.getmtime(f) < cut.timestamp(): continue
        for line in open(f, errors='replace'):
            try: d = json.loads(line)
            except ValueError: continue
            m = d.get('message')
            if d.get('type') != 'assistant' or not isinstance(m, dict): continue
            if not any(isinstance(c, dict) and c.get('type') == 'tool_use' and c.get('name') not in NOOP
                       for c in m.get('content') or []): continue
            try: t = datetime.datetime.fromisoformat(d['timestamp'].replace('Z', '+00:00'))
            except (KeyError, ValueError): continue
            if t >= cut: return True
    return False


def goal(run):
    """(True, what) when the goal looks proved, else (False, why)"""
    P = os.path.join(run, 'home/work')
    try:
        conf = dict(l.strip().split('=', 1) for l in open(os.path.join(run, 'goal/challenge')) if '=' in l)
        stubs = [l.split(':', 1)[1].strip() for l in open(os.path.join(run, 'goal/CHALLENGE.txt'))
                 if l.startswith('omitted:')]
    except OSError:
        return False, 'not a challenge run'
    def git(*a):
        r = subprocess.run(['git', '-c', 'safe.directory=*', '--no-optional-locks', '-C', P, *a],
                           capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else None
    base = conf.get('commit')
    if git('rev-parse', '-q', '--verify', 'refs/tags/final^{commit}'): b = 'final'
    else:
        b = (git('for-each-ref', '--sort=-committerdate', '--format=%(refname:short)', 'refs/heads') or '').split('\n')[0]
    if not base or not b: return False, 'no branch or no challenge commit'
    open_ = [s for s in stubs if re.search(r'\bsorry\b', strip(git('show', '%s:%s' % (base, s)) or ''))]
    if not open_: return False, 'no stub with a sorry in the challenge'
    changed = [f for f in (git('diff', '--name-only', base, b, '--', '*.lean') or '').split('\n') if f]
    left = []
    for f in sorted(set(open_) | set(changed)):
        src = git('show', '%s:%s' % (b, f))
        if src is None:
            if f in open_: left.append(f + ' (missing)')
        elif re.search(r'\bsorry\b', strip(src)): left.append(f)
    if left: return False, '%s has a sorry in %s' % (b, ', '.join(left[:3]) + (' ...' if len(left) > 3 else ''))
    if git('status', '--porcelain', '--untracked-files=no'): return False, 'uncommitted changes in the work tree'
    return True, '%s (%s): no sorry in the stubs or the %d Lean files changed' % (b, (git('rev-parse', '--short', b) or '').strip(), len(changed))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--idle', type=float, default=20); ap.add_argument('--goal-idle', type=float, default=10)
    ap.add_argument('--sample', type=float, default=10); ap.add_argument('--scope'); ap.add_argument('run')
    a = ap.parse_args()
    run = tokens.run_dir(a.run).rstrip('/'); name = os.path.basename(run)
    scope = a.scope or '/sys/fs/cgroup/machine.slice/dsverify-%s.scope' % name
    quiet = last_growth(run)
    if quiet is None: print('NOT DONE: no transcript yet'); return 1
    b = busy(scope, a.sample)
    if b:
        print('NOT DONE: busy: %s' % ', '.join('%s %.1fs' % x for x in b[:5])); return 1
    ok, what = goal(run)
    if ok and quiet >= a.goal_idle:
        print('DONE goal: %s; transcripts quiet for %.0f min' % (what, quiet)); return 0
    if not worked_within(run, a.idle):
        print('DONE idle: no tool call for %g min (goal: %s)' % (a.idle, what)); return 0
    print('NOT DONE: goal: %s; transcripts quiet for %.0f min (goal needs %g); a tool call within %g min'
          % (what, quiet, a.goal_idle, a.idle))
    return 1


if __name__ == '__main__':
    sys.exit(main())
