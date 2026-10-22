//// 参照
//// https://github.com/biuntri/ComProTemplate/blob/main/%E5%85%A5%E5%87%BA%E5%8A%9B%E3%83%86%E3%83%B3%E3%83%97%E3%83%AC.fsx
//// https://github.com/biuntri/ComProTemplate/blob/main/%E6%95%B0%E5%80%A4%E8%A8%88%E7%AE%97%E3%83%86%E3%83%B3%E3%83%97%E3%83%AC.fsx
#if INTERACTIVE
#r "nuget: ac-library-csharp"
#endif

open AtCoder
open System
open System.Collections
open System.Collections.Generic
open System.Linq
open System.IO
open System.Text
open System.Numerics
open System.Diagnostics
open System.Runtime.InteropServices

// 入出力の最適化
let reader = new StreamReader(Console.OpenStandardInput(), bufferSize = 65536);
let writer = new StreamWriter(Console.OpenStandardOutput(), Console.OutputEncoding, 65536);

// 入力用便利メソッド
let readline() = reader.ReadLine()
let readint() = readline() |> int // ~ 2,147,483,647 (2 * 10 ^ 9)
let readint64() = readline() |> int64 // ~ 9,223,372,036,854,775,807 (9 * 10 ^ 18)
let readbigint() = readline() |> bigint.Parse
let readCharArray () = readline().ToCharArray()
let readarray() = readline().Split()
let readarrayint() = readarray() |> Array.map int
let readarrayint64() = readarray() |> Array.map int64
let readarraybigint() = readarray() |> Array.map bigint.Parse
let readlinesfunc func count =
    Array.init count (fun _ -> readline() |> func)
let readlinesint func =
    readlinesfunc (int >> func)
let readlinesint64 func =
    readlinesfunc (int64 >> func)
let readlinesbigint func =
    readlinesfunc (bigint.Parse >> func)
let readlinesCharArray func =
    readlinesfunc (fun x -> x.ToCharArray() |> func)
let readlines01 zero one =
    readlinesCharArray (Array.map (fun c -> 
        match c with
            | c when c = zero -> 0
            | c when c = one -> 1
            | _ -> failwith $"想定されない入力がありました : {c}"
        )
    )
let readlinesarray func =
    readlinesfunc (fun s -> s.Split() |> func)
let readlinesarrayint func =
    readlinesarray (Array.map (int >> func))
let readlinesarrayint64 func =
    readlinesarray (Array.map (int64 >> func))
let readlinesarraybigint func =
    readlinesarray (Array.map (bigint.Parse >> func))

// 出力用便利メソッド
let write ans = writer.WriteLine $"{ans}"
let writeSeq sep Answers =
    Answers
    |> Seq.map string
    |> String.concat sep
    |> writer.WriteLine

let BoolToYESNO b = if b then "YES" else "NO"

let BoolToYesNo b = if b then "Yes" else "No"






writer.Flush()