open System
open System.IO

// ----------------------------------------------------------------------------
// DataTypes
// ----------------------------------------------------------------------------

type BibtexEntry = 
  { Type : string
    Properties : Map<string, string> }

type LatexToken = 
  | Command of string * string option * string option
  | ParagraphBreak
  | Literal of string

type Span = 
  | Endnote of Span list
  | Span of string
  | Teletype of string
  | Reference of string
  | Cite of parenthesize:bool * page:string option * string

type Paragraph = 
  | Heading of level:int * heading:string
  | Paragraph of spans:Span list
  | Image of source:string
  | Caption of label:string option * caption:string
  | Figure of body:Paragraph list
  | Quote of body:Paragraph list
  | Listing of language:string option * body:string
  | InlineBlock of html:string 


// ----------------------------------------------------------------------------
// LaTeX "tokenizer"
// ----------------------------------------------------------------------------

let string cs = System.String(Array.ofSeq cs)

let (|Quoted|_|) qo qc cs =
  let rec loop acc qocount cs =
    match cs with 
    | c::cs when c = qc && qocount = 0 -> Some(List.rev acc, cs)
    | c::cs when c = qc -> loop (c::acc) (qocount - 1) cs
    | c::cs when c = qo -> loop (c::acc) (qocount + 1) cs
    | c::cs -> loop (c::acc) qocount cs
    | [] -> None
  match cs with 
  | c::cs when c = qo ->
      match loop [] 0 cs with 
      | Some(quoted, cs) -> Some(string quoted, cs)
      | _ -> None
  | _ -> None

let (|ZeroOrMore|) f input = 
  let rec loop acc cs = 
    match cs with 
    | c::cs when f c -> loop (c::acc) cs
    | _ -> string (List.rev acc), cs
  loop [] input

let (|OneOrMore|_|) f input = 
  let rec loop acc cs = 
    match cs with 
    | c::cs when f c -> loop (c::acc) cs
    | _ -> List.rev acc, cs
  match loop [] input with 
  | [], _ -> None
  | chars, cs -> Some(string chars, cs)

let rec tokenize acc cs = seq {
  let letterOrAst c = Char.IsLetter(c) || c = '*'
  let notNewLine c = c <> '\n' && c <> '\r'
  let spaceOrTab c = c = ' ' || c = '\t'
  let currentLiteral () = 
    let acc = string(List.rev acc)
    if String.IsNullOrWhiteSpace acc then [] 
    else [ Literal(acc) ]

  match cs with 
  | '\\'::'\\'::Quoted '[' ']' (_, cs) ->
      yield! tokenize acc cs
  | '\\'::(('_' | '#') as c)::cs ->
      yield! tokenize (c::acc) cs
  | '~'::cs ->
      yield! tokenize (List.rev(List.ofSeq "&nbsp;") @ acc) cs

  | '\\'::OneOrMore letterOrAst (cmd, Quoted '{' '}' (args, Quoted '[' ']' (opts, cs))) 
  | '\\'::OneOrMore letterOrAst (cmd, Quoted '[' ']' (opts, Quoted '{' '}' (args, cs))) ->
      yield! currentLiteral ()
      yield Command(cmd, Some opts, Some args)
      yield! tokenize [] cs
  | '\\'::OneOrMore letterOrAst (cmd, Quoted '{' '}' (args, cs)) ->
      yield! currentLiteral ()
      yield Command(cmd, None, Some args)
      yield! tokenize [] cs
  | '\\'::OneOrMore letterOrAst (cmd, cs) ->
      yield! currentLiteral ()
      yield Command(cmd, None, None)
      yield! tokenize [] cs
  | '\r'::'\n'::'\r'::'\n'::cs
  | '\r'::'\n'::OneOrMore spaceOrTab (_, '\r'::'\n'::cs) ->
      yield! currentLiteral ()
      yield ParagraphBreak
      yield! tokenize [] cs
  | '%'::ZeroOrMore notNewLine (_, cs) ->
      yield! tokenize acc cs
  | c::cs -> 
      yield! tokenize (c::acc) cs
  | [] ->
      yield! currentLiteral () }

let formatToken = function
  | ParagraphBreak -> "\r\n\r\n"
  | Literal s -> s
  | Command(name, opts, cmd) -> 
      "\\" + name + (match opts with Some opts -> "[" + opts + "]" | _ -> "")
        + (match cmd with Some cmd -> "{" + cmd + "}" | _ -> "")

// ----------------------------------------------------------------------------
// LaTeX "parser"
// ----------------------------------------------------------------------------

module List = 
  let splitUsing f xs = 
    let rec loop acc xs = 
      match xs with 
      | x::xs when f x -> List.rev acc, x::xs
      | x::xs -> loop (x::acc) xs
      | [] -> List.rev acc, []
    loop [] xs

let (|WhiteSpace|_|) s = 
  if String.IsNullOrWhiteSpace s then Some() else None

let literalToHtml (str:string) = 
  str.Replace("---", "&#8212;").Replace("``", "&#8220;").Replace("''", "&#8221;")

let parseOptions (opts:string option) = 
  match opts with 
  | Some opts -> opts.Split(",") |> Seq.choose (fun kv -> 
      match kv.Split("=") with [|k;v|] ->Some (k, v) | _ -> None) |> dict
  | None -> dict []

let rec parse acc ts = seq {
  let currentParagraph () = 
    if List.isEmpty acc then [] 
    else [ Paragraph(List.rev acc) ]

  match ts with 
  // Environments - code listing (body is text)
  | Command("begin", opts, Some(("lstlisting" | "verbatim") as env))::ts ->
      yield! currentParagraph()
      let opts = parseOptions opts
      let lang = if opts.ContainsKey "language" then Some(opts.["language"]) else None
      let tse, ts = List.splitUsing (function Command("end", _, Some e) -> e = env | _ -> false) ts
      let ts = if ts = [] then failwithf "Missing: \end{%s}" env else List.tail ts
      yield Listing(lang, String.concat "" (Seq.map formatToken tse))
      yield! parse [] ts

  // Environments - minipage, addmargin (ignore)
  | Command("begin", opts, Some(("minipage" | "tiny" | "addmargin") as env))::ts ->
      yield! currentParagraph()
      let tse, ts = List.splitUsing (function Command("end", _, Some e) -> e = env | _ -> false) ts
      let ts = if ts = [] then failwithf "Missing: \end{%s}" env else List.tail ts
      yield! parse [] (tse @ ts)

  // Environments - quote, figure - body is latex
  | Command("begin", opts, Some(env))::ts ->
      yield! currentParagraph()
      let tse, ts = List.splitUsing (function Command("end", _, Some e) -> e = env | _ -> false) ts
      let ts = if ts = [] then failwithf "Missing: \end{%s}" env else List.tail ts
      if env = "figure" then yield Figure(List.ofSeq(parse [] tse))
      elif env = "quote" then yield Quote(List.ofSeq(parse [] tse))
      else failwith $"Unsupported environment: {env}"
      yield! parse [] ts


  // Paragraph-level entities
  | Command(("chapter"|"chapter*"), _, Some heading)::ts -> 
      yield! currentParagraph()
      yield Heading(1, heading)
      yield! parse [] ts
  | Command(("section"|"section*"), _, Some heading)::ts -> 
      yield! currentParagraph()
      yield Heading(2, heading)
      yield! parse [] ts
  | Command("includegraphics", _, Some src)::ts ->
      yield! currentParagraph()
      yield Image(src)
      yield! parse [] ts
  | Command("caption", _, Some cap)::Literal(WhiteSpace _)::Command("label", _, Some lbl)::ts 
  | Command("caption", _, Some cap)::Command("label", _, Some lbl)::ts ->
      yield! currentParagraph()
      yield Caption(Some lbl, literalToHtml cap)
      yield! parse [] ts
  | Command("caption", _, Some cap)::ts ->
      yield! currentParagraph()
      yield Caption(None, cap)
      yield! parse [] ts

  // Span-level entities
  | Command("ref", None, Some ref)::ts ->
      yield! parse (Reference ref::acc) ts  
  | Command("citet", pg, Some cite)::ts ->
      yield! parse (Cite(false, pg, cite)::acc) ts  
  | Command("citep", pg, Some cite)::ts ->
      yield! parse (Cite(true, pg, cite)::acc) ts  
  | Command("ldots", None, None)::ts ->
      yield! parse (Span "&#8230;"::acc) ts
  | Command("endnote", None, Some endnote)::ts ->
      let endnote = parse [] (List.ofSeq (tokenize [] (List.ofSeq endnote))) |> List.ofSeq
      let endnote = match endnote with [ Paragraph p ] -> p | _ -> failwith "endnote - Expected single paragraph"
      yield! parse (Endnote endnote::acc) ts
  | Command("texttt", None, Some body)::ts ->
      let body = body.Replace("\\_", "_")
      yield! parse (Teletype body::acc) ts
  
  // Whitespace & other ignored
  | Command(("vspace" | "quad" | "newpage" | "raisebox" | "noindent"), _, _)::ts ->
      yield! parse acc ts
  | Command(("centering" | "raggedleft" | "theendnotes"), _, _)::ts ->
      yield! parse acc ts

  // Ignored but wrapping things
  | Command("boxed", None, Some body)::ts ->
      let ts = List.ofSeq (tokenize [] (List.ofSeq body)) @ ts
      yield! parse acc ts
 
  // Ignored - keep as latex
  | Command(("textwidth"), _, _)::ts ->
      yield! parse (Span "\textwidth"::acc) ts

  | Command(c, opts, arg)::cs ->
      failwithf "Unsupported command: %s[%A]{%A}\nBefore: %A" c opts arg (List.truncate 10 cs)
  | ParagraphBreak::ts -> 
      yield! currentParagraph()
      yield! parse [] ts
  | Literal(s)::ts ->
      yield! parse (Span(literalToHtml s)::acc) ts 
  | [] -> 
      yield! currentParagraph() }

// ----------------------------------------------------------------------------
// HTML formatting
// ----------------------------------------------------------------------------

type FormattingContext = 
  { NextFootnote : unit -> int 
    References : System.Collections.Generic.IDictionary<string, BibtexEntry> }

let getAuthorAbbr (ref:BibtexEntry) =
  let s = 
    ref.Properties.TryFind "author" 
    |> Option.defaultWith (fun _ -> ref.Properties.["editor"])
  let auths = s.Split(" and ") |> Array.map (fun a -> a.Split(",").[0].Split(' ') |> Seq.last) |> List.ofArray
  match auths with 
  | [a1] -> a1
  | [a1; a2] -> a1 + " and " + a2
  | a1::_ -> a1 + " et al."
  | [] -> failwith "getAuhtorsAbbr: Expected non-empty list"

let rec formatSpans fmt spans = seq { 
  for s in spans do 
    match s with 
    | Teletype(s) -> $"<code>{s}</code>"
    | Cite(paren, pg, cits) ->
        let cits = cits.Split(',') |> Array.map (fun cit ->
          let ref = try fmt.References.[cit] with _ -> failwith $"Cannot find reference: {cit}"
          let year, author = ref.Properties.["year"], getAuthorAbbr ref
          let pgyear = year + if pg.IsSome then ", " + pg.Value else ""
          let link = 
            if paren then author + ", " + pgyear
            else author + " (" + pgyear + ")"
          $"<a href='#{cit}'>{link}</a>")
        if paren then "(" + String.concat "; " cits + ")"
        else String.concat ", " cits

    | Endnote(s) -> 
        let note = fmt.NextFootnote()
        let s = String.concat "" (formatSpans fmt s)
        $"<sup class='noteref'><a href='#note_{note}'>{note}</a></sup>" + 
        $"<span class='note' id='note_{note}'><sup>{note}</sup> {s}</span>"
    | Reference(ref) -> "[#]"
    | Span(s) -> s }

let rec formatPars fmt pars = seq {
  for p in pars do
    match p with 
    | InlineBlock(h) -> 
        yield h
    | Heading(n, h) -> 
        let hname = h.ToLower().Replace(" ", "_")
        yield $"<h{n} id='{hname}'>{h}</h{n}>\n"
    | Caption(lbl, cap) ->  
        yield $"<p><strong>{cap}</strong></p>\n"
    | Image(src) ->
        yield $"<img src=\"{src}\">\n"
    | Paragraph(spans) ->   
        yield "<p>"
        yield! formatSpans fmt spans
        yield "</p>\n\n"
    | Figure(pars) ->
        yield "<div class=\"figure\">\n"
        yield! formatPars fmt pars    
        yield "</div>\n"
    | Quote(pars) ->
        yield "\n<blockquote>\n"
        yield! formatPars fmt pars
        yield "</blockquote>\n\n" 
    | Listing(lang, body) ->
        match lang with 
        | Some lang -> yield $"\n<pre lang=\{lang}\">\n" 
        | None -> yield "\n<pre>\n"
        yield System.Web.HttpUtility.HtmlEncode(body)
        yield "</pre>\n\n" }

let formatGroups fmt groups = seq {
  for pars in groups do
    yield "\n<section>\n"
    yield! formatPars fmt pars
    yield "</section>\n\n"
  }

let groupPars pars = 
  let rec loop acc pars = seq {
    let currentGroup() = 
      if List.isEmpty acc then []
      else [ List.rev acc ]
    match pars with 
    | ((Heading(1, _) | Figure _) as p)::pars ->
        yield! currentGroup ()
        yield [p]
        yield! loop [] pars 
    | (Heading _ as p)::pars ->  
        yield! currentGroup ()
        yield! loop [p] pars
    | p::pars ->
        yield! loop (p::acc) pars 
    | [] ->
        yield! currentGroup () }
  loop [] pars

let generateToc doc = 
  [ for p in doc do
      match p with 
      | Heading(_, h) ->
          let hname = h.ToLower().Replace(" ", "_")
          $"  <li><a href='#{hname}'>{h}</a></li>\n"
      | _ -> () 
    "  <li><a href='#references'>References</a></li>\n" ]
  |> String.concat ""
  |> sprintf "\n<ol>\n%s</ol>\n"
  |> InlineBlock

// ----------------------------------------------------------------------------
// Bibtex parser
// ----------------------------------------------------------------------------

let (|Find|_|) k map = 
  Map.tryFind k map

let (|Identifier|_|) cs = 
  let rec loop acc cs = 
    match cs with 
    | c::cs when Char.IsLetterOrDigit(c) || c = '-' || c = '_' -> loop (c::acc) cs
    | cs when not (List.isEmpty acc) -> Some(string (List.rev acc), cs)
    | _ -> None
  loop [] cs

let sconc sep s1 s2 =
  if String.IsNullOrWhiteSpace s1 then s2 
  elif String.IsNullOrWhiteSpace s2 then s1 
  else s1 + sep + s2

let optconc sep s1 s2 = 
  match s2 with None -> s1 | Some s2 -> sconc sep s1 s2

let (+|) = sconc ", "
let (+|?) = optconc ", "
let (+-) = sconc " "
let (+-?) = optconc " "
let (+.) = sconc ". "
let (+.?) = optconc ". "

let rec skipWhite cs = 
  match cs with 
  | c::cs when Char.IsWhiteSpace c -> skipWhite cs
  | _ -> cs

let (|SkipWhite|) cs = skipWhite cs

let rec readBibValue literal acc cs = 
  match cs with 
  | '\\'::'l'::'d'::'o'::'t'::'s'::cs -> readBibValue literal (List.rev (List.ofSeq "&#8230;") @ acc) cs
  | '\\'::'#'::cs -> readBibValue literal ('#' :: acc) cs
  | '\\'::'$'::cs -> readBibValue literal ('$' :: acc) cs
  | '\\'::'&'::cs -> readBibValue literal ('&' :: acc) cs
  | ' '::cs when literal -> readBibValue literal (';'::'2'::'3'::'#'::'&'::acc) cs
  | '\\'::'u'::'r'::'l'::Quoted '{' '}' (url, cs) -> 
      let link = $"<a href='{url}'>{url}</a>" |> Seq.toList |> List.rev
      readBibValue literal (link @ acc) cs
  | '{'::cs -> readBibValue true acc cs
  | '}'::cs -> readBibValue false acc cs
  | c::cs -> readBibValue literal (c::acc) cs
  | [] -> string (List.rev acc)

let rec readDefs acc cs = 
  match skipWhite cs with 
  | Identifier(id, SkipWhite('='::SkipWhite(Identifier(value, (','::cs | cs)))))
  | Identifier(id, SkipWhite('='::SkipWhite(Quoted '"' '"' (value, (','::cs | cs))))) 
  | Identifier(id, SkipWhite('='::SkipWhite(Quoted '{' '}' (value, (','::cs | cs))))) ->
      let value = readBibValue false [] (List.ofSeq value)
      readDefs ((id, value)::acc) cs
  | '}'::cs -> 
      Map.ofList acc, cs
  | _ -> failwith $"Expected key/value or end, but found: {string (Seq.truncate 200 cs)}..."

let rec readBib acc cs = 
  match skipWhite cs with 
  | '@'::Identifier(typ, '{'::Identifier(key, ','::cs)) ->
      let props, cs = readDefs [] cs
      readBib ((key, { Type = typ.ToLower(); Properties = props })::acc) cs
  | [] ->
      acc
  | _ -> failwith $"Expected entry, but found: {string (Seq.truncate 200 cs)}..."

let formatAuthorList (s:string) =
  [ for a in s.Split(" and ") -> a.Split(",") |> Seq.map (_.Trim()) |> Seq.rev |> String.concat " " ]
  |> String.concat ", "

let renderReferences refs = 
  let endw (c:char) (s:string) = 
    if not(String.IsNullOrWhiteSpace s) && not(s.EndsWith(',')) 
      && not(s.EndsWith('.')) && not(s.EndsWith('?')) then s + (c.ToString()) else s
  let refs = refs |> Seq.map (fun (key, ref) ->
    let title = ref.Properties.["title"]
    let year = ref.Properties.["year"]
    let authAbbr = getAuthorAbbr ref

    let auth, ed =
      match ref.Properties with 
      | Find "author" author & Find "editor" editor -> 
          formatAuthorList author, formatAuthorList editor + ", editor"
      | Find "author" author -> formatAuthorList author, ""
      | Find "editor" editor -> formatAuthorList editor + " (ed.)", ""
      | _ -> failwith "Missing author and editor"
    
    let pub, det = 
      match ref.Type with 
      | "book" -> 
          ref.Properties.["publisher"] +|? ref.Properties.TryFind("address"),
          "" +-? ref.Properties.TryFind("isbn") +.? ref.Properties.TryFind("note")
      | "misc" -> 
          ref.Properties.["howpublished"],
          "" +-? ref.Properties.TryFind("note")
      | "inproceedings" | "incollection" | "inbook" -> 
          "In " +-? 
            Option.map (sprintf "%s, editor, ") (ref.Properties.TryFind("editor")) +
            ref.Properties.["booktitle"] +-?
            Option.map (sprintf "(%s)") (ref.Properties.TryFind("series")) +|?
            Option.map (sprintf "pages %s") (ref.Properties.TryFind("pages")) +|?
            ref.Properties.TryFind("address")
          , "" +-? ref.Properties.TryFind("publisher") +|? 
            Option.map (sprintf "ISBN %s") (ref.Properties.TryFind("isbn")) +|? 
            Option.map (fun d -> sprintf "doi <a href='https://dx.doi.org/%s'>%s</a>" d d) 
              (ref.Properties.TryFind("doi")) +.? 
            ref.Properties.TryFind("note")
      | "article" ->
          ref.Properties.["journal"] +|? ref.Properties.TryFind("volume") +-?
            Option.map (sprintf "(%s)") (ref.Properties.TryFind("number")) +|?
            Option.map (sprintf "pages %s") (ref.Properties.TryFind("pages"))
          , "" +|?             
            Option.map (fun d -> sprintf "doi <a href='https://dx.doi.org/%s'>%s</a>" d d) 
              (ref.Properties.TryFind("doi")) +|? 
            ref.Properties.TryFind("publisher") +|? ref.Properties.TryFind("address") +.? 
            ref.Properties.TryFind("note")
      | "phdthesis" ->
          "PhD thesis, " + ref.Properties.["school"]
          , "" +|? ref.Properties.TryFind("note")
      | "techreport" ->
          "Technical Report " + ref.Properties.["number"] +|? 
          ref.Properties.TryFind("institution") +|? ref.Properties.TryFind("address")
          , "" +|? ref.Properties.TryFind("note")

      | typ -> failwith $"Unsupported bib item type: {typ}"
    
    authAbbr + " (" + year + ")",
    $"<li class='pub'><span class='author'>{endw '.' auth} </span>" + 
    $"<span id='{key}'><span class='title'>{endw '.' title}</span></span> " + 
    $"{endw '.' pub} {endw '.' year} {det}</a></li>\n"
  )
  let refs = refs |> Seq.sortBy fst |> Seq.map snd
  let body = String.concat "\n" refs
  InlineBlock("<h2 id='references'>References</h2>\n<ul>" + body + "</ul>")

// ----------------------------------------------------------------------------
// Main
// ----------------------------------------------------------------------------

let output = Path.Combine(__SOURCE_DIRECTORY__, "output")
let figOutput = Path.Combine(__SOURCE_DIRECTORY__, "output", "fig")
let figSource = Path.Combine(__SOURCE_DIRECTORY__, "..", "fig")
Directory.CreateDirectory(output)
if Directory.Exists figOutput then try Directory.Delete(figOutput, true) with _ -> ()
Directory.CreateDirectory(figOutput)
for f in Directory.GetFiles(figSource) do File.Copy(f, f.Replace(figSource, figOutput))

let latex = Path.Combine(__SOURCE_DIRECTORY__, "..", "chapters", "introduction.tex")
let bibtex = Path.Combine(__SOURCE_DIRECTORY__, "..", "main.bib")
let template = Path.Combine(__SOURCE_DIRECTORY__, "template.html")
let header = Path.Combine(__SOURCE_DIRECTORY__, "header.html")
let index = Path.Combine(__SOURCE_DIRECTORY__, "output", "index.html")

let bib = File.ReadAllText(bibtex)
let refs = readBib [] (List.ofSeq bib)

let counter() = 
  let mutable n = 0
  fun () -> n <- n + 1; n

let fmt = { NextFootnote = counter(); References = dict refs }
let chars = File.ReadAllText(latex)
let tokens = tokenize [] (List.ofSeq chars) |> List.ofSeq
let doc = parse [] tokens |> List.ofSeq

let groups = 
  let groups = doc |> groupPars |> List.ofSeq
  let toc = doc |> Seq.tail |> generateToc
  let head = InlineBlock(File.ReadAllText(header))
  [ head; toc ] :: (List.tail groups) @ [[ renderReferences refs ]]

let html = groups |> formatGroups fmt |> String.concat ""
File.WriteAllText(index, File.ReadAllText(template).Replace("{{content}}", html))

