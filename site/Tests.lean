import DocSite.Check

open DocSite

private def ensure (condition : Bool) : IO Unit := do
  unless condition do throw <| IO.userError "Documentation regression failed"

private def expectFailure (action : IO Unit) : IO Unit := do
  let failed ← try action; pure false catch _ => pure true
  unless failed do throw <| IO.userError "Expected a failing check"

def main : IO Unit := do
  ensure <| fillTemplate "$body $footer" #[("body", "$footer"), ("footer", "F")] == "$footer F"
  let .ok (heading, body) := renderPage "# waterfall\n\nPage content."
    | throw <| IO.userError "Page title was not extracted"
  ensure <| containsText heading "<h1>waterfall</h1>"
  ensure <| containsText body "Page content." && !containsText body "<h1>"
  ensure <| !(renderPage "## Missing page title").isOk
  let page := htmlMetadata "<!-- <a href='bad'> --><script>const x = '<a href=bad>';</script><div id='α'><a title='a > b' href=\"a&amp;b.html#x\">link</a><img src=photo.png>"
  ensure <| page.ids == #["α"]
  ensure <| page.links == #["a&b.html#x", "photo.png"]
  ensure <| decodeUrl "caf%C3%A9%20x#y" == "café x#y"
  let rendered := renderMarkdown "| Option | Value |\n| --- | --- |\n| mode | search |\n\n<details>\n<summary>Proof</summary>\n\n```lean\nimport waterfall\n```\n\n</details>"
  ensure <| containsText rendered "<table>" && containsText rendered "<details>"
  ensure <| containsText rendered "language-lean"
  ensure <| (leanBlocks (GFMarkdown.parseDocument "> ```lean\n> import waterfall\n> ```")).size == 1
  let complete : Example := {source := "index.md", code := "import waterfall\nexample : True := by\n  waterfall\n"}
  ensure <| !(prepareExamples #[complete, {source := "index.md", code := "example : False := by waterfall"}] "index.md").isOk
  ensure <| (prepareExamples #[complete, {source := "index.md", code := "waterfall (effort := 2)"}] "index.md").isOk
  IO.FS.withTempDir fun dir => do
    let page := dir / "index.html"
    IO.FS.writeFile page "<div id='café'></div>"
    checkLink page "#caf%C3%A9"
    expectFailure (checkLink page "#missing")
    expectFailure (checkLink page "missing.html")
    IO.FS.writeFile page "<div id='x'></div><span id=x></span>"
    expectFailure (discard <| readMetadata page)
  IO.println "Documentation rendering, links, anchors and excerpt checks pass."
