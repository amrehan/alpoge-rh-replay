"""Profile indexed project work from an existing inventory and Lake logs; never run builds."""
import argparse
from collections import Counter, defaultdict, deque
import json
import math
from pathlib import Path
import re
from statistics import median

import replay_evidence as evidence
import tasks


ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\S+\s+\[\d+/\d+\]\s+Built\s+([^\s:]+)(?::olean)?(?:\s+\(([^)]+)\))?\s*$')
TIME = re.compile(r'(\d+(?:\.\d+)?)(ms|s)')
LIMITATIONS = [
    'Object presence is scheduling guidance, not verified reuse; stale artifacts may require rebuilding.',
    'Log timings are rounded elapsed module times, hardware- and contention-specific, not CPU costs.',
    'The model assumes fixed module durations and ideal scheduling; it is not a forecast or full-proof ETA.',
    'Transfers, cache preparation, grant/review delays, statement/axiom audits and final fresh-kernel replay are excluded.',
]


def parse_timings(paths, module_ids):
    samples = defaultdict(list)
    for path in paths:
        with Path(path).open(errors='replace') as stream:
            for number, line in enumerate(stream, 1):
                match = BUILT.fullmatch(ANSI.sub('', line).strip())
                if not match or match[1] not in module_ids or match[2] is None:
                    continue
                duration = TIME.fullmatch(match[2])
                if not duration:
                    raise ValueError(f'{path}:{number}: Invalid module timing {match[2]!r}')
                seconds = float(duration[1]) / (1000 if duration[2] == 'ms' else 1)
                if not math.isfinite(seconds):
                    raise ValueError(f'{path}:{number}: Nonfinite module timing')
                samples[module_ids[match[1]]].append(seconds)
    return samples


def graph(rows):
    by_id = {row['id']: row for row in rows}
    if not by_id or len(by_id) != len(rows):
        raise ValueError('The module index must be nonempty and have unique IDs')
    if len({row['module'] for row in rows}) != len(rows):
        raise ValueError('The module index contains duplicate module names')
    imports = {task: sorted(set(row['imports'])) for task, row in by_id.items()}
    consumers = defaultdict(list)
    for task, dependencies in imports.items():
        for dependency in dependencies:
            if dependency not in by_id:
                raise ValueError(f'Unknown import {dependency} of {task}')
            consumers[dependency].append(task)
    remaining = {task: len(dependencies) for task, dependencies in imports.items()}
    ready = deque(task for task, count in remaining.items() if not count)
    order = []
    depth = {}
    while ready:
        task = ready.popleft()
        order.append(task)
        depth[task] = 1 + max((depth[d] for d in imports[task]), default=-1)
        for consumer in consumers[task]:
            remaining[consumer] -= 1
            if remaining[consumer] == 0:
                ready.append(consumer)
    if len(order) != len(rows):
        raise ValueError('The import graph contains a cycle')
    return by_id, imports, order, depth


def profile(rows, cached, samples, slots=1, assume_seconds=None, include_module_timings=False):
    if type(slots) is not int or slots <= 0:
        raise ValueError('Slots must be a positive integer')
    if assume_seconds is not None and (not math.isfinite(assume_seconds) or assume_seconds <= 0):
        raise ValueError('Assumed module seconds must be positive and finite')
    by_id, imports, order, depth = graph(rows)
    cached = set(cached)
    if cached - by_id.keys():
        raise ValueError('Unknown inventory IDs: ' + ', '.join(sorted(cached - by_id.keys())[:5]))
    if samples.keys() - by_id.keys():
        raise ValueError('Timing observations contain unknown module IDs')
    durations = {}
    for task, observations in samples.items():
        if not observations or any(not math.isfinite(t) or t < 0 for t in observations):
            raise ValueError('Invalid timing observations for ' + task)
        durations[task] = median(observations)
    missing = by_id.keys() - cached
    timed = missing & durations.keys()
    unknown = missing - durations.keys()
    chain = {}
    for task in order:
        # Cached nodes cost zero, but do not cut off their potentially missing imports.
        chain[task] = int(task in missing) + max((chain[d] for d in imports[task]), default=0)
    report = dict(scope='Object-presence and log-timing profile of all indexed project modules.',
                  modules=len(rows), cached_modules=len(cached), missing_modules=len(missing),
                  requested_slots=slots,
                  max_import_depth=max(depth.values()),
                  missing_modules_by_depth=dict(sorted(Counter(depth[t] for t in missing).items())),
                  longest_missing_dependency_chain_modules=max(chain.values()),
                  timing_coverage=dict(timed_project_modules=len(durations), timed_missing_modules=len(timed),
                      missing_without_timings=len(unknown), observations=sum(map(len, samples.values())),
                      fraction_of_missing=round(len(timed) / len(missing), 6) if missing else 1.0,
                      aggregation='Median elapsed duration per module; shared dependencies counted once.'),
                  limitations=list(LIMITATIONS), idealized_model=None)
    if include_module_timings:
        report['module_timings'] = {task: dict(median_seconds=round(durations[task], 6),
                                             observations=len(samples[task]))
                                    for task in sorted(durations)}
    if unknown and assume_seconds is None:
        report['model_unavailable_reason'] = 'Missing module durations; provide logs or explicitly request an assumption scenario.'
        return report
    weights = {task: durations.get(task, assume_seconds) if task in missing else 0.0 for task in order}
    weighted_path = {}
    predecessor = {}
    for task in order:
        previous = max(imports[task], key=lambda d: (weighted_path[d], d), default=None)
        predecessor[task] = previous
        weighted_path[task] = weights[task] + (weighted_path[previous] if previous else 0)
    end = max(order, key=lambda t: (weighted_path[t], t))
    path = []
    cursor = end
    while cursor is not None:
        if cursor in missing:
            path.append(cursor)
        cursor = predecessor[cursor]
    total = math.fsum(weights.values())
    if not math.isfinite(total) or not math.isfinite(weighted_path[end]):
        raise ValueError('Timing model overflow')
    effective_slots = min(slots, len(missing))
    per_slot = total / effective_slots if effective_slots else 0.0
    report['idealized_model'] = dict(kind='assumption_scenario' if unknown else 'observed_timing_model',
        requested_slots=slots, effective_slots=effective_slots, assumed_modules=len(unknown),
        assume_module_seconds=assume_seconds, total_module_seconds=round(total, 6),
        weighted_critical_path_seconds=round(weighted_path[end], 6),
        work_per_slot_seconds=round(per_slot, 6),
        idealized_lower_bound_seconds=round(max(weighted_path[end], per_slot), 6),
        critical_path_ids=list(reversed(path)))
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inventory', type=Path)
    parser.add_argument('--log', action='append', default=[], type=Path, help='existing Lake build log; repeat')
    parser.add_argument('--slots', type=int, default=1, help='effective parallel module slots for the model')
    parser.add_argument('--assume-module-seconds', type=float, help='explicit scenario duration for unobserved modules')
    parser.add_argument('--include-module-timings', action='store_true', help='include per-module median seconds and sample counts')
    args = parser.parse_args(argv)
    try:
        inventory = evidence.read_inventory(args.inventory)
        if not inventory['identity']['platform'] or len(set(inventory['modules'])) != len(inventory['modules']):
            raise ValueError('Invalid inventory platform or duplicate module IDs')
        rows = list(tasks.module_rows())
        samples = parse_timings(args.log, {row['module']: row['id'] for row in rows})
        report = profile(rows, inventory['modules'], samples, args.slots, args.assume_module_seconds,
                         args.include_module_timings)
        def reference(path):
            return dict(name=path.name, sha256=tasks.digest(path))
        report['inputs'] = dict(inventory=reference(args.inventory), logs=list(map(reference, args.log)),
                               identity=inventory['identity'])
        if 'worker_scope' in inventory:
            report['inputs']['worker_scope'] = inventory['worker_scope']
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError) as error:
        print(json.dumps(dict(status='invalid', error=str(error))))
        return 2
    print(json.dumps(report, indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
