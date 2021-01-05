import os, shutil
BUILD = 'build'
OUTDIR = 'output'
os.makedirs(OUTDIR, exist_ok=True)
for root, dirs, files in os.walk(BUILD):
    if 'document.pdf' in files:
        segments = root.split('/')
        assert segments[0] == BUILD
        assert segments[-1] == 'output'
        segments = segments[1:-1]
        filename = '-'.join(segments) + '.pdf'
        path = '/'.join([OUTDIR] + segments[:-1])
        os.makedirs(path, exist_ok=True)
        shutil.copy(root + '/document.pdf', path + '/' + filename)
