import json, glob, collections, statistics as st
E = '/home/ubuntu/.claude/jobs/f5d25fd8/tmp/exp'
H = json.load(open(E + '/runs/harness.json'))
rows = [json.load(open(p)) for p in glob.glob(E + '/results/*.json')]
order = ['items__insertAt', 'items__find', 'node__split', 'node__get', 'node__insert']
agg = collections.defaultdict(list)
for r in rows:
    # cost in output-token equivalents of the input side (cache reads 0.02, writes 0.25, fresh 0.2)
    r['cost_in'] = r['cache_read'] * 0.02 + r['cache_write'] * 0.25 + r['input_fresh'] * 0.2
    r['harness_tokens'] = H[r['run']]['subagent_tokens']
    agg[(r['challenge'], r['condition'])].append(r)
def m(rs, k):
    return st.mean(x[k] for x in rs)
print('| challenge | condition | solved | wall min | compiler wait min | checks | API turns | input tokens (M, incl. cache) | input cost (k out-eq.) | proof lines |')
print('|---|---|---|---|---|---|---|---|---|---|')
tot = collections.defaultdict(lambda: collections.defaultdict(float))
for ch in order:
    for cond in ['base', 'treat']:
        rs = agg[(ch, cond)]
        line = (f"| {ch.replace('__', '.')} | {'baseline' if cond == 'base' else 'tools'} | {sum(r['pass'] for r in rs)}/{len(rs)} | "
                f"{m(rs, 'wall_min'):.1f} | {m(rs, 'tool_wait_min'):.1f} | {m(rs, 'checks'):.1f} | {m(rs, 'api_messages'):.0f} | "
                f"{m(rs, 'input_total') / 1e6:.2f} | {m(rs, 'cost_in') / 1e3:.0f} | {m(rs, 'grade_lines'):.0f} |") if False else None
        for r in rs:
            r['grade_lines'] = r['grade']['proof_lines']
        print(f"| {ch.replace('__', '.')} | {'baseline' if cond == 'base' else 'tools'} | {sum(r['pass'] for r in rs)}/{len(rs)} | "
              f"{m(rs, 'wall_min'):.1f} | {m(rs, 'tool_wait_min'):.1f} | {m(rs, 'checks'):.1f} | {m(rs, 'api_messages'):.0f} | "
              f"{m(rs, 'input_total') / 1e6:.2f} | {m(rs, 'cost_in') / 1e3:.0f} | {m(rs, 'grade_lines'):.0f} |")
        for k in ['wall_min', 'tool_wait_min', 'checks', 'api_messages', 'input_total', 'cost_in']:
            tot[cond][k] += sum(r[k] for r in rs)
print()
print('| totals (20 runs) | wall min | compiler wait min | checks | API turns | input tokens (M) | input cost (k out-eq.) |')
print('|---|---|---|---|---|---|---|')
for cond in ['base', 'treat']:
    t = tot[cond]
    print(f"| {cond} | {t['wall_min']:.0f} | {t['tool_wait_min']:.1f} | {t['checks']:.0f} | {t['api_messages']:.0f} | {t['input_total'] / 1e6:.1f} | {t['cost_in'] / 1e3:.0f} |")
b, t = tot['base'], tot['treat']
print('ratio tools/base:', {k: round(t[k] / b[k], 2) for k in b})
