open System
open System.IO
open System.Diagnostics

let FILE = "main.tex"
let PDFLATEX = @"C:\Programs\Publishing\MiKTeX 2.9\miktex\bin\x64\pdflatex.exe"
let BIBTEX = @"C:\Programs\Publishing\MiKTeX 2.9\miktex\bin\x64\bibtex.exe"
let SUMATRAPDF = @"C:\Programs\Publishing\SumatraPDF\SumatraPDF.exe"

let path = __SOURCE_DIRECTORY__

let logf clr fmt = Printf.kprintf (fun s ->
  Console.ForegroundColor <- clr
  printfn "[%s] %s" (DateTime.Now.ToLongTimeString()) s) fmt

let updateTex() =
  logf ConsoleColor.DarkGray "running latex"
  let ps =
    ProcessStartInfo
      ( FileName = PDFLATEX,
        Arguments = "-interaction=nonstopmode " + FILE,
        WorkingDirectory = path,
        UseShellExecute = false,
        CreateNoWindow = true )
  let p = Process.Start(ps)
  p.WaitForExit()
  logf (if p.ExitCode <> 0 then ConsoleColor.DarkRed else ConsoleColor.DarkGreen)
    "pdflatex completed (%d)" p.ExitCode

let updateBib() =
  logf ConsoleColor.DarkGray "running bibtex"
  let run () =
    let ps =
      ProcessStartInfo
        ( FileName = BIBTEX,
          Arguments = FILE.Replace(".tex", ""),
          WorkingDirectory = path,
          UseShellExecute = false,
          CreateNoWindow = true )
    let p = Process.Start(ps)
    p.WaitForExit()
    logf (if p.ExitCode <> 0 then ConsoleColor.DarkRed else ConsoleColor.DarkGreen)
      "bibtex completed (%d)" p.ExitCode
  run ()
  updateTex ()
  run ()
  updateTex ()
  run ()
  updateTex ()

type UpdateMessage = UpdateTex | UpdateBib

let agent = MailboxProcessor.Start(fun inbox -> async {
  while true do
    try
      match! inbox.Receive() with
      | UpdateTex -> updateTex ()
      | UpdateBib -> updateBib ()
    with e ->
      logf ConsoleColor.DarkRed "agent error %s" e.Message
})

let watchTex() =
  let fsw = new FileSystemWatcher(path,"*.tex",IncludeSubdirectories=true)
  fsw.Changed.Add(fun e ->
    logf ConsoleColor.DarkGray "watchTex: %A [%A]" e.Name e.ChangeType
    agent.Post(UpdateTex) )
  fsw.EnableRaisingEvents <- true
  fsw

let watchBib() =
  let fsw = new FileSystemWatcher(path,"*.bib",IncludeSubdirectories=true)
  fsw.Changed.Add(fun e ->
    logf ConsoleColor.DarkGray "watchBib: %A [%A]" e.Name e.ChangeType
    agent.Post(UpdateBib) )
  fsw.EnableRaisingEvents <- true
  fsw

let ps =
  ProcessStartInfo
    ( FileName = SUMATRAPDF,
      Arguments = "\"" + __SOURCE_DIRECTORY__ + "\\" + FILE.Replace(".tex", ".pdf") + "\"",
      WorkingDirectory = path )

updateTex ()
Process.Start(ps) |> ignore
updateBib ()
let f1 = watchTex ()
let f2 = watchBib ()

System.Threading.Thread.Sleep(System.Threading.Timeout.Infinite)
