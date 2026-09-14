import GFMarkdown

namespace DocSite
open System

/-- The content stays in Markdown; this list only supplies page titles. -/
def pages : Array (String × String) :=
  #[("index", "Induction proofs in Lean"), ("examples", "Examples")]

def outputDir (root : FilePath) : FilePath := root / "dist/site"

def renderMarkdown (source : String) : String := Id.run do
  let mut html := GFMarkdown.renderHtml (GFMarkdown.parseDocument source)
  html := html.replace "href=\"../" "href=\"source/"
  for (name, _) in pages do
    let target := if name == "index" then "./" else name ++ ".html"
    html := html.replace s!"href=\"{name}.md\"" s!"href=\"{target}\""
    html := html.replace s!"href=\"{name}.md#" s!"href=\"{target}#"
  return html

/-- Substitute the frame once, preserving literal dollar names in page content. -/
def fillTemplate (source : String) (fields : Array (String × String)) : String :=
  let parts := source.splitOn "$"
  parts.head! ++ String.join ((parts.drop 1).map fun part =>
    let chars := part.toList
    let key := chars.takeWhile (fun c => c.isAlpha || c == '_')
    match fields.find? (·.1 == String.ofList key) with
    | some (_, value) => value ++ String.ofList (chars.drop key.length)
    | none => "$" ++ part)

/-- Copy bytes so that downloadable compressed logs retain their original contents. -/
partial def copyTree (source target : FilePath) : IO Unit := do
  if ← source.isDir then
    IO.FS.createDirAll target
    for entry in ← source.readDir do
      unless entry.fileName == "__pycache__" || entry.path.extension == some "pyc" do
        copyTree entry.path (target / entry.fileName)
  else
    IO.FS.writeBinFile target (← IO.FS.readBinFile source)

/-- Works from the repository root, docbuild/, or an explicitly supplied directory. -/
partial def findRoot (directory : FilePath) : IO FilePath := do
  let directory ← IO.FS.realPath directory
  if (← (directory / "Waterfall.lean").pathExists) &&
      (← (directory / "site/index.md").pathExists) then return directory
  match directory.parent with
  | some parent =>
    if parent == directory then throw <| IO.userError "Waterfall repository not found"
    findRoot parent
  | none => throw <| IO.userError "Waterfall repository not found"

/-- Only dist/site is replaced. No generated HTML is checked into the repository. -/
def build (root : FilePath) : IO Unit := do
  let source := root / "site"
  let output := outputDir root
  if ← output.pathExists then IO.FS.removeDirAll output
  IO.FS.createDirAll output
  let template ← IO.FS.readFile (source / "_template.html")
  let footer := renderMarkdown (← IO.FS.readFile (source / "footer.md"))
  for (name, title) in pages do
    let current := " aria-current=\"page\""
    let html := fillTemplate template #[
      ("title", Html.escape title),
      ("overview_current", if name == "index" then current else ""),
      ("examples_current", if name == "examples" then current else ""),
      ("footer", footer),
      ("body", renderMarkdown (← IO.FS.readFile (source / s!"{name}.md"))) ]
    IO.FS.writeFile (output / s!"{name}.html") html
  for name in #["style.css", "guide.html", "reference.html"] do
    copyTree (source / name) (output / name)
  IO.FS.createDirAll (output / "source")
  for name in #["Docs", "Waterfall", "Tests", "docs", "LICENSE"] do
    copyTree (root / name) (output / "source" / name)
  IO.println s!"Built {output / "index.html"}"

end DocSite
