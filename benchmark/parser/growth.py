#!/usr/bin/env python3
"""Generate separate module-count and lexical-inventory cold parser controls.

Only parser fixtures: propositions have no proofs and are never verified.
No new syntax is exported by consumers. Labels differ, token bodies do not.
"""
import argparse
import json
from pathlib import Path


def name(i):
    return 'bench' + ''.join(chr(97 + i // (26 ** power) % 26) for power in [2, 1, 0])


def generate(output, modules, blocks, syntax):
    output.mkdir(parents=True, exist_ok=False)
    roots = []
    for axis in ['modules', 'syntax']:
        for scale in [1, 2, 4]:
            directory = output / f'{axis}-{scale}'
            directory.mkdir()
            count = modules * (scale if axis == 'modules' else 1)
            inventory = syntax * (scale if axis == 'syntax' else 1)
            declarations = []
            for i in range(inventory):
                # Distinct entry tokens, a shared prefix, and a literal/hole tail.
                surface = [name(i), 'common ' + name(i), name(i) + ' over $y$'][i % 3]
                declarations.append('\\begin{abbreviation}\\label{syntax_' + name(i) + '}\n'
                                    '$x$ is ' + surface + ' iff $x=x$.\n\\end{abbreviation}\n')
            (directory / 'provider.tex').write_text(''.join(declarations))
            for m in range(count):
                text = '\\import{' + str((directory / 'provider.tex').resolve().relative_to(Path.cwd())) + '}\n'
                for b in range(blocks):
                    body = ['$x$ is benchaaa.', '$x$ is common benchaab.', '$x$ is benchaac over $y$.'][b % 3]
                    text += ('\\begin{proposition}\\label{consumer_' + name(m) + '_' + name(b) + '}\n'
                             + body + '\n\\end{proposition}\n')
                (directory / f'consumer-{m}.tex').write_text(text)
            root = directory / 'root.tex'
            root.write_text(''.join('\\import{' + str((directory / f'consumer-{m}.tex').resolve().relative_to(Path.cwd()))
                                    + '}\n' for m in range(count)))
            roots.append({'name': f'{axis}-{scale}', 'root': str(root.resolve()),
                          'axis': axis, 'scale': scale, 'consumers': count,
                          'blocks_per_consumer': blocks, 'syntax_declarations': inventory})
    (output / 'manifest.json').write_text(json.dumps(roots, indent=2) + '\n')
    return roots


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('output', type=Path)
    p.add_argument('--modules', type=int, default=8)
    p.add_argument('--blocks', type=int, default=128)
    p.add_argument('--syntax', type=int, default=48)
    args = p.parse_args()
    if args.modules <= 0 or args.blocks <= 0 or args.syntax < 3 or args.syntax * 4 > 26 ** 3:
        p.error('positive counts, at least three syntax entries, and at most 26^3 names required')
    generate(args.output, args.modules, args.blocks, args.syntax)
