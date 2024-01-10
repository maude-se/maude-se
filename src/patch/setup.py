from skbuild import setup

with open("build/PythonPkgDescription.md", "r") as fh:
    long_description = fh.read()

setup(
    name='maude-se',
    version='0.0.1',
    author='Geunyeol Yu',
    author_email='maude-se@postech.ac.kr',
    description='Maude SMT Extension',
    long_description=long_description,
    url='https://github.com/maude-se/maude-se',
    project_urls={
        'Bug Tracker'   : 'https://github.com/maude-se/maude-se/issues',
        'Documentation' : 'https://maude-se.github.io',
        'Source Code'   : 'https://github.com/maude-se/maude-se'
    },
    long_description_content_type="text/markdown",
    license='GPLv2',
    packages=['maudeSE'],
    scripts=["../src/maude-se"],
    classifiers=[
         'Intended Audience :: Science/Research',
         'Programming Language :: Python',
         'Programming Language :: Python :: 3',
         'Topic :: Scientific/Engineering',
         'Operating System :: OS Independent',
     ]
)
