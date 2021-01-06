import os, shutil, re
from deploy import pdf_path
from nice_names import NICE_NAMES

URL_PREFIX = 'https://github.com/NieDzejkob/isabelle-math-contests/blob/built-pdfs/'
BUILD = 'build/'

ROOT_TEMPLATE = """
session "{session_name}" in "{directory}" = Common +
  options [document = pdf, document_output = "output"]
  theories
    "{name}"
  document_files
    "root.tex"
"""

rootfile_snippet = ''
TAGS_REGEX = re.compile(r'\(\* TAGS: (.*) \*\)')
README_REGEX = re.compile(r'^.*BEGIN DYNAMIC CONTENT (.|\n)* END DYNAMIC CONTENT.*$', re.MULTILINE)

def read_tags(filename):
    with open(filename) as f:
        taglines = TAGS_REGEX.findall(f.read())
    return sum((line.split() for line in taglines), [])

problems = {}

def prepare_name(name, nice=False):
    if name in NICE_NAMES:
        return NICE_NAMES[name]
    else:
        return name.replace('_', ' ')

class Problem:
    def __init__(self, origin, pdf, tags):
        self.pdf = pdf
        self.tags = tags
        self.origin = origin

    def tag_list(self):
        return ', '.join(tag.replace('-', ' ') for tag in self.tags)

    def entry(self, origin):
        return f'- [{origin}]({self.pdf}) ({self.tag_list()})'

    def entry_by_origin(self):
        return self.entry(prepare_name(self.origin[-1], True))

    def entry_by_tag(self):
        return self.entry(' '.join(map(prepare_name, self.origin)))

def remember_problem(path):
    pdf = URL_PREFIX + pdf_path(path)
    tags = read_tags(path + '.thy')
    path = path.split('/')

    dictionary = problems
    for component in path[:-1]:
        if component not in dictionary:
            dictionary[component] = {}
        dictionary = dictionary[component]

    dictionary[path[-1]] = Problem(path, pdf, tags)

def indent(x):
    return '  ' + x.replace('\n', '\n  ')

def make_fold(header, contents):
    return "- <details>\n" + indent(f"<summary>{header}</summary>\n\n{contents}\n</details>")

def make_category(header, contents):
    return f"- {header}\n{indent(contents)}"

def render_dict(name, dictionary, top=False):
    contents = ''
    total_folded = 0
    total_problems = 0
    for entry_name, value in sorted(dictionary.items()):
        if type(value) is dict:
            md, folded, problems = render_dict(entry_name, value)
            contents += md
            total_folded += folded
            total_problems += problems
        else:
            contents += value.entry_by_origin()
            total_folded += 1
            total_problems += 1
        contents += '\n'
    should_fold = top or total_folded >= 10

    name = prepare_name(name, True)
    if should_fold:
        problems = 'problems' if total_problems > 1 else 'problem'
        md = make_fold(name + f" [<i>{total_problems} {problems}</i>]", contents)
        total_folded = 1
    else:
        md = make_category(name, contents)
    return md, total_folded, total_problems

if __name__ == "__main__":
    shutil.rmtree(BUILD, ignore_errors=True)

    for root, dirs, files in os.walk('.'):
        if root == '.':
            continue
        assert root.startswith('./')
        root = root[2:]
        for f in files:
            if f.endswith('.thy'):
                name = f[:-4]

                path = root + '/' + name
                directory = BUILD + path
                os.makedirs(directory + '/document')
                shutil.copy(root + '/' + f, directory + '/' + f)
                shutil.copy('root.tex', directory + '/document/root.tex')

                session_name = root.replace('/', '-') + '-' + name
                rootfile_snippet += ROOT_TEMPLATE.format(
                    directory=directory,
                    session_name=session_name,
                    name=name)

                remember_problem(path)

    with open('ROOT', 'a') as f:
        f.write(rootfile_snippet)

    readme_snippet = '## Problems by origin\n\n'
    for name, value in sorted(problems.items()):
        readme_snippet += render_dict(name, value, True)[0] + '\n'

    os.makedirs('output', exist_ok=True)
    with open('README.md') as f:
        readme = f.read()
    readme = README_REGEX.sub(readme_snippet, readme)
    with open('output/README.md', 'w') as f:
        f.write(readme)
