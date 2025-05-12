'''
SageMath module.
Tools for the shuffle theorem and variants.
'''


import os
import subprocess
import sys


if sys.platform in ['win32', 'win64']:
    # Use PowerShell instead of CMD on Windows.
    os.system = lambda msg: subprocess.call(['powershell.exe', msg], stdout=sys.stdout)


def _create_latex(latex, filename='latexfile', folder='LaTeX', pdf_viewer=None):
    '''
    Generate and compiles a LaTeX file with content from a 'latex' source string.
    Files are located in $HOME/LaTeX (can be changed through the 'folder' variable).
    Can specify a pdf viewer by passing the corresponding command line executable.
    '''

    # Create the folder.
    os.system(f'mkdir -p {folder}')

    # Create the LaTeX file.
    with open(f'{folder}/{filename}.tex', 'w') as f:
        f.write(latex)

    # Compiles the LaTeX file, then deletes the 'Temp' folder, recreates it with all the new files.
    # If pdf_viewer is set to None, it uses the deafult one.
    os.system(f'pdflatex -interaction=batchmode {folder}/{filename}.tex')
    os.system('rm ' + '-r ' + folder + '/Temp')
    os.system(f'mkdir {folder}/Temp')
    os.system(f'code {folder}/{filename}.tex &')
    os.rename(f'{folder}/{filename}.tex', f'{folder}/Temp/{filename}.tex')
    os.rename(f'{filename}.pdf', f'{folder}/Temp/{filename}.pdf')
    os.rename(f'{filename}.log', f'{folder}/Temp/{filename}.log')
    os.rename(f'{filename}.aux', f'{folder}/Temp/{filename}.aux')

    run_in_background = ''

    if pdf_viewer is None:
        if sys.platform in ['win32', 'win64']:  # Windows environment
            pdf = 'start'
        elif sys.platform == 'darwin':  # MacOS environment
            pdf = 'open'
        elif sys.platform in ['linux', 'linux2']:  # Linux environment
            pdf = 'xdg-open'
            run_in_background = '&'
        elif sys.platform == 'cygwin':  # Sage environment
            pdf = 'cygstart'
        else:
            raise EnvironmentError('OS not supported.')
    else:
        pdf = pdf_viewer

    os.system(f'{pdf} {folder}/Temp/{filename}.pdf {run_in_background}')

    return None


def draw(items, filename='paths', folder='LaTeX', columns=4, latex_options=None, pdf_viewer=None):
    '''
    Converts an iterator into a pdf/latex file.
    Possibly displays some extra information, depending on latex options.


    # The variable set should be an iterator of objects with a tex() module.
    # Set columns to n (default is 4) to display n objects in each row.
    # Set aword, stats to True to display the area word, and the values of the selected statistics respectively.
    # Set pdf to a command line pdf viewer to open and view the pdf file with the selected viewer.
    # The default value None uses the system default viewer.
    '''

    latex = ''  # latex is a string containing the text of the tex file.
    latex += '\\documentclass[varwidth=\\maxdimen]{standalone}\n'
    latex += '\\usepackage{xcolor}\n'
    latex += '\\usepackage{tikz}\n\n'

    latex += '\\begin{document}\n\n'
    latex += '\\vspace*{1cm} \\begin{center} \\textsc{Number of objects: %d} \\end{center} \n\n' % (len(items))

    for column, s in enumerate(items, start=1):
        if latex_options is not None:
            s.set_latex_options(latex_options)

        latex += s._latex_()

        if column % columns == 0:  # Breaks line after 'cols' columns.
            latex += '\\newline\n'
    latex += '\\end{document}'

    _create_latex(latex, filename=filename, folder=folder, pdf_viewer=pdf_viewer)

    return None
