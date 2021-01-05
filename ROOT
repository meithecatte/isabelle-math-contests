session Useful_Deps in ".." = "HOL-Analysis" +
  sessions
    "HOL-Number_Theory"
    "HOL-Algebra"
  theories
    "HOL-Number_Theory.Number_Theory"
    "HOL-Algebra.Algebra"

session Common = Useful_Deps +
  theories
    Future_Library
    Cyclic_Groups
    Dihedral_Groups

session "OM-1969-Stage1" in "om/1969/stage1" = Common +
  options [document = pdf, document_output = "output"]
  theories
    "WarmupI"
    "SeriesI"
    "SeriesII"
  document_files
    "root.tex"

session "OM-2020-Stage1" in "om/2020/stage1" = Common +
  options [document = pdf, document_output = "output"]
  theories
    "SeriesI"
  document_files
    "root.tex"

session "Napkin" in "napkin" = Common + 
  options [document = pdf, document_output = "output"]
  theories
    "Chapter1"
  document_files
    "root.tex"
