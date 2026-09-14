import DocSite.Check

/-- No Python or root-package dependency is needed to build or check the site. -/
def main (args : List String) : IO UInt32 := do
  try
    let root ← DocSite.findRoot (System.FilePath.mk (args[1]?.getD "."))
    match args.head? with
    | some "build" => DocSite.build root
    | some "check" => DocSite.checkSite root
    | some "check-docs" => DocSite.checkDocs root
    | _ =>
      IO.eprintln "Usage: site {build|check|check-docs} [repository-directory]"
      return 1
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
