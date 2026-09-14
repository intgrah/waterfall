import CommonMark.Parser.Inline

namespace DocSite
open CommonMark.Parser

structure PageMetadata where
  links : Array String := #[]
  ids : Array String := #[]
  deriving Repr, BEq

/-- Decode character references in attribute values without treating backslashes as escapes. -/
def decodeEntities (source : String) : String := Id.run do
  let mut chars := source.toList
  let mut out := ""
  while !chars.isEmpty do
    match chars with
    | '&' :: rest =>
      if let some (value, tail) := parseEntityRef rest then
        out := out ++ value
        chars := tail
      else
        out := out.push '&'
        chars := rest
    | c :: rest => out := out.push c; chars := rest
    | [] => break
  return out

/-- CommonMark validates the attribute syntax; here we retain its name and value. -/
def attributeValue (chars : List Char) : String × String := Id.run do
  let chars := chars.dropWhile Char.isWhitespace
  let name := chars.takeWhile isAttrNameChar
  let rest := (chars.drop name.length).dropWhile Char.isWhitespace
  let value := match rest with
    | '=' :: rest =>
      let rest := rest.dropWhile Char.isWhitespace
      match rest with
      | '"' :: cs => cs.takeWhile (· != '"')
      | '\'' :: cs => cs.takeWhile (· != '\'')
      | cs => cs.takeWhile isUnquotedAttrValueChar
    | _ => []
  return (String.ofList name |>.toLower, decodeEntities (String.ofList value))

/-- Inspect actual start tags, including embedded HTML from Markdown. Comments,
quoted `>` characters and raw-text elements must not introduce spurious links. -/
def htmlMetadata (source : String) : PageMetadata := Id.run do
  let mut chars := source.toList
  let mut out : PageMetadata := {}
  while !chars.isEmpty do
    match chars with
    | '<' :: rest =>
      chars := rest
      if let some (_, tail) := matchInlineHtml rest then
        chars := tail
        if rest.head?.any isTagNameStart then
          let name := rest.takeWhile isTagNameChar
          let mut attrs := rest.drop name.length
          while true do
            let some tail := parseAttr attrs | break
            let (key, value) := attributeValue (attrs.take (attrs.length - tail.length))
            if key == "id" then out := {out with ids := out.ids.push value}
            if key == "href" || key == "src" then out := {out with links := out.links.push value}
            attrs := tail
          let tag := (String.ofList name).toLower
          if #["script", "style", "textarea", "title"].contains tag then
            if let some (before, _) := findNeedle (s!"</{tag}>".toList) (chars.map Char.toLower) then
              chars := chars.drop (before.length + tag.length + 3)
    | _ :: rest => chars := rest
    | [] => break
  return out

/-- URL escapes describe UTF-8 bytes, not Unicode character numbers. -/
def decodeUrl (source : String) : String := Id.run do
  let bytes := source.toUTF8
  let mut out := ByteArray.empty
  let mut i := 0
  while i < bytes.size do
    if bytes[i]! == 37 && i + 2 < bytes.size then
      let digit (b : UInt8) : Option Nat :=
        let n := b.toNat
        if 48 ≤ n && n ≤ 57 then some (n - 48)
        else if 65 ≤ n && n ≤ 70 then some (n - 55)
        else if 97 ≤ n && n ≤ 102 then some (n - 87)
        else none
      if let (some hi, some lo) := (digit bytes[i+1]!, digit bytes[i+2]!) then
        out := out.push (hi * 16 + lo).toUInt8
        i := i + 3
        continue
    out := out.push bytes[i]!
    i := i + 1
  return (String.fromUTF8? out).getD source

end DocSite
