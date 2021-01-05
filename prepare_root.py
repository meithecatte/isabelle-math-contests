import os, shutil

BUILD = 'build/'

TEMPLATE = """
session "{session_name}" in "{directory}" = Common +
  options [document = pdf, document_output = "output"]
  theories
    "{name}"
  document_files
    "root.tex"
"""

shutil.rmtree(BUILD, ignore_errors=True)

for root, dirs, files in os.walk('.'):
    if root == '.':
        continue
    assert root.startswith('./')
    root = root[2:]
    for f in files:
        if f.endswith('.thy'):
            name = f[:-4]

            directory = BUILD + root + '/' + name
            os.makedirs(directory + '/document')
            shutil.copy(root + '/' + f, directory + '/' + f)
            shutil.copy('root.tex', directory + '/document/root.tex')

            session_name = root.replace('/', '-') + '-' + name
            print(TEMPLATE.format(directory=directory, session_name=session_name, name=name))
