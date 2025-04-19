open System
open System.IO

// ----------------------------------------------------------------------------
// LaTeX "tokenizer"
// ----------------------------------------------------------------------------

type LatexToken = 
  | Command of string * string option * string option
  | ParagraphBreak
  | Literal of string

let string cs = System.String(Array.ofSeq cs)

let (|Quoted|_|) qo qc cs =
  let rec loop acc cs =
    match cs with 
    | c::cs when c = qc -> Some(List.rev acc, cs)
    | c::cs -> loop (c::acc) cs
    | [] -> None
  match cs with 
  | c::cs when c = qo ->
      match loop [] cs with 
      | Some(quoted, cs) -> Some(string quoted, cs)
      | _ -> None
  | _ -> None

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
    if List.isEmpty acc then [] 
    else [ Literal(string(List.rev acc)) ]

  match cs with 
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
  | '%'::OneOrMore notNewLine (_, cs) ->
      yield! tokenize acc cs
  | c::cs -> 
      yield! tokenize (c::acc) cs
  | [] ->
      yield! currentLiteral () }

// ----------------------------------------------------------------------------
// LaTeX "parser"
// ----------------------------------------------------------------------------

type Span = 
  | Endnote of string
  | Span of string
  | Reference of string

type Paragraph = 
  | Heading of level:int * heading:string
  | Paragraph of spans:Span list
  | Image of source:string
  | Caption of label:string option * caption:string
  | Environment of name:string * body:Paragraph list

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

let literalToSpan (str:string) = 
  Span(str.Replace("---", "&#8212;").Replace("``", "&#8220;").Replace("''", "&#8221;"))

let rec parse acc ts = seq {
  let currentParagraph () = 
    if List.isEmpty acc then [] 
    else [ Paragraph(List.rev acc) ]

  match ts with 
  // Environments
  | Command("begin", _, Some env)::ts ->
      yield! currentParagraph()
      let tse, ts = List.splitUsing (function Command("end", _, Some e) -> e = env | _ -> false) ts
      let ts = if ts = [] then failwithf "Missing: \end{%s}" env else List.tail ts
      yield Environment(env, List.ofSeq(parse [] tse))
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
      yield Caption(Some lbl, cap)
      yield! parse [] ts
  | Command("caption", _, Some cap)::ts ->
      yield! currentParagraph()
      yield Caption(None, cap)
      yield! parse [] ts

  // Span-level entities
  | Command("ref", None, Some ref)::ts ->
      yield! parse (Reference ref::acc) ts  
  | Command("ldots", None, None)::ts ->
      yield! parse (Span "&#8230;"::acc) ts
  | Command("endnote", None, Some endnote)::ts ->
      yield! parse (Endnote endnote::acc) ts
  
  // Whitespace
  | Command(("vspace" | "quad" | "newpage"), _, _)::ts ->
      yield! parse acc ts

  | Command(c, opts, arg)::_ ->
      failwithf "Unsupported command: %s[%A]{%A}" c opts arg
  | ParagraphBreak::ts -> 
      yield! currentParagraph()
      yield! parse [] ts
  | Literal(s)::ts ->
      yield! parse (literalToSpan s::acc) ts 
  | [] -> 
      yield! currentParagraph() }

// ----------------------------------------------------------------------------
// HTML formatting
// ----------------------------------------------------------------------------

let formatSpans spans = seq { 
  for s in spans do 
    match s with 
    | Endnote(s) -> "[^]"
    | Reference(ref) -> "[#]"
    | Span(s) -> s }

let rec formatPars pars = seq {
  for p in pars do
    match p with 
    | Heading(n, h) -> 
        yield $"<h{n}>{h}</h{n}>\n"
    | Caption(lbl, cap) ->  
        yield $"<p><strong>{cap}</strong></p>\n"
    | Image(src) ->
        yield $"<img src=\"{src}\">"
    | Paragraph(spans) ->   
        yield "<p>"
        yield! formatSpans spans
        yield "</p>\n"
    | Environment("figure", pars) ->
        yield "<div class=\"figure\">\n"
        yield! formatPars pars    
        yield "</div>\n"
    | Environment("quote", pars) ->
        yield "\n<blockquote>\n"
        yield! formatPars pars
        yield "</blockquote>\n\n" 
    | Environment(env, _) ->
        failwith $"Unsupported environment: {env}" }

// ----------------------------------------------------------------------------
// Main
// ----------------------------------------------------------------------------

let output = Path.Combine(__SOURCE_DIRECTORY__, "output")
let figOutput = Path.Combine(__SOURCE_DIRECTORY__, "output", "fig")
let figSource = Path.Combine(__SOURCE_DIRECTORY__, "..", "fig")
if Directory.Exists output then Directory.Delete(output, true)
Directory.CreateDirectory(output)
Directory.CreateDirectory(figOutput)
for f in Directory.GetFiles(figSource) do File.Copy(f, f.Replace(figSource, figOutput))

let latex = Path.Combine(__SOURCE_DIRECTORY__, "..", "chapters", "introduction.tex")
let template = Path.Combine(__SOURCE_DIRECTORY__, "template.html")
let index = Path.Combine(__SOURCE_DIRECTORY__, "output", "index.html")

let chars = File.ReadAllText(latex).[0 .. 10000] 
let tokens = tokenize [] (List.ofSeq chars) |> List.ofSeq
let doc = parse [] tokens |> List.ofSeq
let html = doc |> formatPars |> String.concat ""
File.WriteAllText(index, File.ReadAllText(template).Replace("{{content}}", html))

