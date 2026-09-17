import DocSite.Build
import DocSite.Html

namespace DocSite
open System

def containsText (text part : String) : Bool := part.isEmpty || (text.splitOn part).length > 1

def readMetadata (path : FilePath) : IO PageMetadata := do
  let data := htmlMetadata (← IO.FS.readFile path)
  let mut seen : Array String := #[]
  for id in data.ids do
    if seen.contains id then throw <| IO.userError s!"Duplicate anchor in {path}: {id}"
    seen := seen.push id
  return data

/-- Check local destinations. External URLs are left for deployment verification;
Markdown fragments use the hosting platform's heading rules and are not checked here. -/
def checkLink (source : FilePath) (url : String) : IO Unit := do
  if url.startsWith "//" || containsText ((url.splitOn "#").head!) ":" then return
  let parts := url.splitOn "#"
  let path := decodeUrl (((parts.head!).splitOn "?").head!)
  let fragment := decodeUrl (String.intercalate "#" (parts.drop 1))
  let mut target := if path.isEmpty then source else source.parent.getD "." / path
  if ← target.isDir then target := target / "index.html"
  unless ← target.pathExists do throw <| IO.userError s!"Broken link: {source} -> {url}"
  if !fragment.isEmpty && target.extension == some "html" then
    unless (← readMetadata target).ids.contains fragment do
      throw <| IO.userError s!"Broken anchor: {source} -> {url}"

def checkSite (root : FilePath) : IO Unit := do
  build root
  let mut count := 0
  for entry in ← (outputDir root).readDir do
    if entry.path.extension == some "html" then
      for link in (← readMetadata entry.path).links do
        checkLink entry.path link
        count := count + 1
  IO.println s!"Website links and anchors pass ({count} links inspected)."

/-- Traversing the parsed blocks also finds fences inside lists and block quotes. -/
partial def leanBlocks (blocks : GFMarkdown.Document) : Array String := Id.run do
  let mut out := #[]
  for block in blocks do
    match block with
    | .codeBlock (some info) text =>
      if info.trimAscii.toString == "lean" then out := out.push text
    | .blockQuote blocks => out := out ++ leanBlocks blocks
    | .list _ _ items =>
      for (_, blocks) in items do out := out ++ leanBlocks blocks
    | _ => pure ()
  return out

structure Example where
  source : FilePath
  code : String
  deriving Repr, Inhabited

/-- Complete fences are independent files. Excerpts must agree with one of them;
option-only invocations are tested on the main page's complete traversal example. -/
def prepareExamples (blocks : Array Example) (mainPage : FilePath) : Except String (Array Example) := do
  let complete := blocks.filter (·.code.startsWith "import ")
  let some traversal := complete.find? (·.source == mainPage)
    | throw "Main page has no complete Lean example"
  let mut out := complete
  for sample in blocks do
    if sample.code.startsWith "import " then continue
    if sample.code.startsWith "waterfall " then
      let pieces := traversal.code.splitOn "  waterfall"
      if pieces.length < 2 then throw "Main example has no waterfall invocation"
      let proofPrelude := String.intercalate "  waterfall" pieces.dropLast
      let tactic := String.intercalate "\n" (sample.code.trimAscii.toString.splitOn "\n" |>.map ("  " ++ ·))
      out := out.push {sample with code := proofPrelude ++ tactic ++ "\n"}
    else if !complete.any (fun full => containsText full.code sample.code.trimAscii.toString) then
      throw s!"Excerpt differs from the complete examples in {sample.source}:\n{sample.code}"
  return out

/-- Parse source Markdown for both ordinary and reference-style links. Rendering
also lets the same HTML metadata check inspect raw anchors and links in these files. -/
def documentationExamples (root : FilePath) : IO (Array Example) := do
  let mut documents := #[root / "README.md", root / "site/README.md", root / "site/footer.md"]
  for entry in ← (root / "docs").readDir do
    if entry.path.extension == some "md" then documents := documents.push entry.path
  for (name, _) in pages do documents := documents.push (root / "site" / s!"{name}.md")
  let mut blocks := #[]
  for path in documents do
    let document := GFMarkdown.parseDocument (← IO.FS.readFile path)
    for link in (htmlMetadata (GFMarkdown.renderHtml document)).links do
      -- Main-page .html destinations only exist after rendering. In source,
      -- page-to-page links are written as .md links and resolve normally.
      if !link.startsWith "#" then checkLink path link
    if path == root / "README.md" || pages.any (fun (name, _) => path == root / "site" / s!"{name}.md") then
      blocks := blocks ++ (leanBlocks document).map (fun code => {source := path, code})
  match prepareExamples blocks (root / "site/index.md") with
  | .ok examples => return examples
  | .error error => throw <| IO.userError error

/-- The documentation executable uses its own toolchain. Each child proof check
explicitly selects the parent package's toolchain and drops inherited Lake paths. -/
def checkDocs (root : FilePath) : IO Unit := do
  checkSite root
  let examples ← documentationExamples root
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  IO.FS.withTempDir fun directory => do
    for i in [:examples.size] do
      let sample := examples[i]!
      let path := directory / s!"Example{i}.lean"
      IO.FS.writeFile path sample.code
      IO.println s!"Checking example {i + 1} from {sample.source}"
      let child ← IO.Process.spawn {
        cmd := "elan", args := #["run", toolchain, "lake", "env", "lean", path.toString], cwd := root,
        env := #[ ("ELAN_TOOLCHAIN", none), ("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
          ("LEAN_SYSROOT", none) ] }
      let status ← child.wait
      unless status == 0 do throw <| IO.userError s!"Example check failed: {sample.source} (exit {status})"
  IO.println s!"Documentation links and {examples.size} README/website examples pass."

end DocSite
