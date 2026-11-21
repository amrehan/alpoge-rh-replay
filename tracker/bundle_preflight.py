"""Diagnose conflicting build-archive members without extracting or installing them."""
import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


BLOCK = 1024 * 1024
SCOPE = 'Archive byte-difference diagnostic only; does not establish proof validity or receiver reuse.'


class HashingReader:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()

    def read(self, size=-1):
        block = self.stream.read(size)
        self.digest.update(block)
        return block


def canonical_name(name, directory=False):
    original = name
    if not name or '\\' in name or '\0' in name or name.startswith('/'):
        raise ValueError('Unsafe member path: ' + repr(name))
    while name.startswith('./'):
        name = name[2:]
    if directory and name.endswith('/'):
        name = name[:-1]
    if directory and name in ('', '.'):
        return ''
    if any(part in ('', '.', '..') for part in name.split('/')):
        raise ValueError('Unsafe member path: ' + repr(original))
    path = PurePosixPath(name)
    if (path.parts[:2] != ('lib', 'lean') and path.parts[:1] != ('ir',)
            and not (directory and path.parts == ('lib',))):
        raise ValueError('Expected a lib/lean/ or ir/ artifact: ' + repr(original))
    return name


def module_name(name):
    path = PurePosixPath(name)
    if path.parts[:2] == ('lib', 'lean'):
        parts = path.parts[2:]
    elif path.parts[:1] == ('ir',):
        parts = path.parts[1:]
    else:
        raise ValueError('Expected a lib/lean/ or ir/ artifact: ' + repr(name))
    if not parts or '.' not in parts[-1] or not parts[-1].split('.', 1)[0]:
        raise ValueError('Expected a module artifact filename: ' + repr(name))
    return '.'.join((*parts[:-1], parts[-1].split('.', 1)[0]))


def scan(path, expected):
    if not re.fullmatch(r'[0-9a-fA-F]{64}', expected):
        raise ValueError('Expected SHA-256 must contain 64 hexadecimal characters: ' + str(path))
    expected = expected.lower()
    members = {}
    with Path(path).open('rb') as raw:
        reader = HashingReader(raw)
        with gzip.GzipFile(fileobj=reader, mode='rb') as decoded:
            with tarfile.open(fileobj=decoded, mode='r|') as archive:
                for member in archive:
                    name = canonical_name(member.name, member.isdir())
                    if member.isdir():
                        continue
                    module = module_name(name)
                    if name in members:
                        raise ValueError('Duplicate member path: ' + repr(name))
                    if (member.type not in (tarfile.REGTYPE, tarfile.AREGTYPE)
                            or member.sparse is not None or member.size < 0):
                        raise ValueError('Nonregular member: ' + repr(member.name))
                    digest = hashlib.sha256()
                    # extractfile returns a read-only stream, never a filesystem path.
                    with archive.extractfile(member) as stream:
                        for block in iter(lambda: stream.read(BLOCK), b''):
                            digest.update(block)
                    members[name] = (module, digest.hexdigest())
                # Do not silently ignore a second archive or hidden members
                # after the first tar end marker. Normal tar padding is zero.
                for block in iter(lambda: archive.fileobj.read(BLOCK), b''):
                    if block.strip(b'\0'):
                        raise ValueError('Nonzero data after the tar end marker: ' + str(path))
            # Tar iteration can finish before the gzip footer. Drain the decoder
            # to validate its CRC/length and hash every compressed input byte.
            while decoded.read(BLOCK):
                pass
        while reader.read(BLOCK):
            pass
        actual = reader.digest.hexdigest()
    if actual != expected:
        raise ValueError(f'Archive SHA-256 mismatch for {path}: expected {expected}, got {actual}')
    return actual, members


def preflight(archives):
    provenance = []
    files = defaultdict(lambda: defaultdict(list))
    modules = {}
    for index, (path, expected) in enumerate(archives):
        actual, members = scan(path, expected)
        provenance.append(dict(index=index, path=str(path), sha256=actual, members=len(members)))
        for name, (module, digest) in members.items():
            files[name][digest].append(index)
            modules[name] = module
    conflicts = defaultdict(list)
    traces = defaultdict(list)
    setups = defaultdict(list)
    for name, variants in sorted(files.items()):
        if len(variants) > 1:
            # Traces and generated compiler inputs include metadata such as
            # checkout paths. Keep raw differences visible but informational.
            group = (traces if name.endswith('.trace') else setups
                     if name.endswith('.setup.json') else conflicts)
            group[modules[name]].append(dict(path=name, variants=[
                dict(sha256=digest, archives=indices) for digest, indices in sorted(variants.items())
            ]))
    return dict(scope=SCOPE,
                status='conflicts' if conflicts else 'metadata_differences' if traces or setups else 'clear',
                archives=provenance,
                summary=dict(archives=len(provenance), unique_members=len(files),
                             overlapping_members=sum(sum(map(len, variants.values())) > 1
                                                     for variants in files.values()),
                             conflicting_members=sum(map(len, conflicts.values())),
                             conflicting_modules=len(conflicts),
                             differing_trace_members=sum(map(len, traces.values())),
                             differing_setup_members=sum(map(len, setups.values()))),
                conflicts=[dict(module=module, files=members)
                           for module, members in sorted(conflicts.items())],
                trace_differences=[dict(module=module, files=members)
                                   for module, members in sorted(traces.items())],
                setup_differences=[dict(module=module, files=members)
                                   for module, members in sorted(setups.items())])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', action='append', nargs=2, required=True,
                        metavar=('PATH', 'SHA256'), help='gzip tar archive and its expected SHA-256; repeat')
    args = parser.parse_args(argv)
    if len(args.archive) < 2:
        parser.error('Supply at least two --archive arguments')
    try:
        report = preflight(args.archive)
    except (OSError, EOFError, tarfile.TarError, ValueError) as error:
        report = dict(scope=SCOPE, status='invalid', error=str(error))
        code = 2
    else:
        code = 1 if report['conflicts'] else 0
    print(json.dumps(report, indent=2, sort_keys=True))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
