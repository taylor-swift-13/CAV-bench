#!/usr/bin/env python3
"""Render the author-confirmed publication aggregates without changing run logs."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    data = json.loads((ROOT / 'figures/publication_results.json').read_text())
    lines = []
    previous = None
    best = max(r['correct'] for r in data['rows'])

    def cell(x, y):
        return f'{x:.1f}' + r'\,\nontimeoutcost{' + f'{y:.1f}' + '}'

    def pair(a, b, c, d, second='.1f'):
        return (f'{a:.1f}/' + format(b, second) + r'\,\nontimeoutcost{'
                + f'{c:.1f}/' + format(d, second) + '}')

    for r in data['rows']:
        if previous is not None and previous != r['group']:
            lines.append(r'\addlinespace[2.2pt]')
        if previous != r['group']:
            lines.append(r'\textit{' + r['group'] + r'} & & & & & & & & & \\')
        previous = r['group']
        p, n = r['avg_tool_profile_solved'], r['avg_tool_profile_non_timeout']
        rate = f"{100 * r['correct'] / 140:.1f}"
        if r['correct'] == best:
            rate = r'\textbf{' + rate + '}'
        values = [r'\quad ' + r['model'] + ' (' + r['effort'] + ')',
                  f"{r['correct']}/140", f"{r['wrong']}/{r['reported_timeouts']}", rate,
                  cell(r['avg_minutes_solved'], r['avg_minutes_non_timeout']),
                  pair(r['avg_input_tokens_m_solved'], r['avg_output_tokens_k_solved'],
                       r['avg_input_tokens_m_non_timeout'], r['avg_output_tokens_k_non_timeout'], '.0f'),
                  pair(p['read'], p['write'], n['read'], n['write']),
                  cell(p['total'], n['total']),
                  pair(p['coqc'], p['vcg'], n['coqc'], n['vcg']),
                  cell(p['rounds'], n['rounds'])]
        lines.append(' & '.join(values) + r' \\')
    (ROOT / 'tables/main_results.tex').write_text('\n'.join(lines + [r'\bottomrule']) + '\n')

    lines, previous = [], None
    for r in data['failure_rows']:
        if previous is not None and previous != r['group']:
            lines.append(r'\addlinespace[2.2pt]')
        if previous != r['group']:
            lines.append(r'\textit{' + r['group'] + r'} & & & \\')
        previous = r['group']
        lines.append(r'\quad ' + r['model'] + ' (' + r['effort'] + ') & '
                     + f"{r['failure']}/{r['timeout']} & {r['proof']}/{r['vcg']} & "
                     + f"{r['invalid_proof']}/{r['input_modification']}/{r['prohibited_read']}" + r' \\')
    totals = {k: sum(r[k] for r in data['failure_rows'])
              for k in ['failure', 'timeout', 'proof', 'vcg', 'invalid_proof',
                        'input_modification', 'prohibited_read']}
    total_cells = [r'\textbf{Total}']
    for keys in [('failure', 'timeout'), ('proof', 'vcg'),
                 ('invalid_proof', 'input_modification', 'prohibited_read')]:
        total_cells.append(r'\textbf{' + '/'.join(str(totals[k]) for k in keys) + '}')
    lines.extend([r'\midrule', ' & '.join(total_cells) + r' \\', r'\bottomrule'])
    (ROOT / 'tables/error_analysis_models.tex').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
