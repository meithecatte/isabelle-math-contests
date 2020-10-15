session Useful_Deps in ".." = "HOL-Analysis" +
  sessions
    "HOL-Number_Theory"
  theories
    "HOL-Number_Theory.Number_Theory"

session Future_Library = Useful_Deps +
  theories
    Future_Library

session "OM-1969-Stage1" in "om/1969/stage1" = Future_Library +
  options [document = pdf, document_output = "output"]
  theories
    "WarmupI"
    "SeriesI"
    "SeriesII"
  document_files
    "root.tex"

session "OM-2020-Stage1" in "om/2020/stage1" = Useful_Deps +
  options [document = pdf, document_output = "output"]
  theories
    "SeriesI"
  document_files
    "root.tex"
