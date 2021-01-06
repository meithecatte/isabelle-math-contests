import os, shutil
BUILD = 'build'
OUTDIR = 'output'

# takes a directory path and returns the corresponding PDF path
def pdf_path(root):
    segments = root.split('/')
    if segments[0] == BUILD:
        segments = segments[1:]
    if segments[-1] == 'output':
        segments = segments[:-1]

    filename = '-'.join(segments) + '.pdf'
    return '/'.join(segments[:-1] + [filename])

def copy_pdf(root):
    path = pdf_path(root)
    os.makedirs(path, exist_ok=True)
    shutil.copy(root + '/document.pdf', OUTDIR + '/' + path)

if __name__ == "__main__":
    os.makedirs(OUTDIR, exist_ok=True)
    for root, dirs, files in os.walk(BUILD):
        if 'document.pdf' in files:
            copy_pdf(root)
