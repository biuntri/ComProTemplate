open System.Collections.Generic

// グラフ走査
// neighbors (場所 -> (場所, コスト) seq ) : 隣接しているノード
// Found (場所 -> bool) : ゴールに到達したか
// push (ルート -> コスト -> メモ -> unit) : メモへの入力 (queueなら Enqueue)
// pop (メモ -> (ルート, コスト)) : メモからの出力 (queueなら Dequeue)
// note (ルート(逆順) * コスト) : メモを入れておくもの
// 返り値 : bool
let inline GraphTraversal (start: ^p) (neighbors: ^p -> (^p * ^c) seq) (Found: ^p -> bool) (push: ^p list -> ^c -> ^n -> unit) (tryPop: ^n -> (^p list * ^c) option) (note: ^n): (^p list * ^c) option =
    let zerocost = LanguagePrimitives.GenericZero

    // 初期値設定
    let exprored: Dictionary<^p,^p list> = Dictionary()
    let inList = Dictionary()
    push [start] zerocost note
    inList.Add (start, [start])

    // 探索実行
    // exprored: 探索済み
    let rec loop (exprored: Dictionary<^p, ^p list>) (inList: Dictionary<^p, ^p list>) (note: ^n) : (^p list * ^c) option =
        let nextoption = tryPop note
        match nextoption with
        | None -> None
        | Some (next, cost) ->
            if Found next.Head then
                Some (next, cost)
            else
                let neighbor = neighbors next.Head
                exprored.Add (next.Head, next)
                for n in neighbor do
                    let p, c = n
                    let route = p :: next
                    if not (exprored.ContainsKey p || inList.ContainsKey p) then
                        push route (c + cost) note
                        inList.Add (p, route)
                loop exprored inList note
    
    loop exprored inList note


/// 深さ優先探索
let inline DepthFirstSearch neighbors start found =
    let Collection = Stack<^p list>()

    let inline push (pos: ^p list) _ (collection: Stack<^p list>) = collection.Push pos

    let inline TryPop (collection: Stack<^p list>) : (^p list * ^c) option =
        let ok, result = collection.TryPop()

        if ok then
            Some(result, LanguagePrimitives.GenericOne)
        else
            None

    GraphTraversal start neighbors found push TryPop Collection

/// 幅優先探索
let inline WidthFirstSearch neighbors start found =
    let Collection = Queue<^p list>()

    let inline push (pos: ^p list) _ (collection: Queue<^p list>) = collection.Enqueue pos

    let inline TryPop (collection: Queue<^p list>) : (^p list * ^c) option =
        let ok, result = collection.TryDequeue()

        if ok then
            Some(result, LanguagePrimitives.GenericOne)
        else
            None

    GraphTraversal start neighbors found push TryPop Collection

// ダイクストラ法
// 単独で動く
let inline ShortestPathFirstSearch neighbors (start: ^p) found =
    let Collection = PriorityQueue<^p list, ^c>()

    let inline push (pos: ^p list) cost (collection: PriorityQueue<^p list, ^c>) =
        collection.Enqueue (pos, cost)

    let inline TryPop (collection: PriorityQueue<^p list, ^c>) : (^p list * ^c) option =
        let ok, result, cost = collection.TryDequeue ()
        if ok then
            Some (result, cost)
        else
            None

    let zerocost = LanguagePrimitives.GenericZero

    // 初期値設定
    let exprored: Dictionary<^p,^c * ^p list> = Dictionary()
    push [start] zerocost Collection

    // 探索実行
    // exprored: 探索済み
    let rec loop (exprored: Dictionary<^p, ^c * ^p list>) (note: PriorityQueue<^p list, ^c>) : (^p list * ^c) option =
        let nextoption = TryPop note
        match nextoption with
        | None -> None
        | Some (next, cost) ->
            if found next.Head then
                Some (next, cost)
            else
                let neighbor = neighbors next.Head
                if not (exprored.ContainsKey next.Head) then
                    exprored.Add (next.Head, (cost, next))
                    for n in neighbor do
                        let p, c = n
                        let route = p :: next
                        push route (c + cost) note
                    loop exprored  note
                elif exprored.[next.Head] |> fst > cost then
                    exprored.[next.Head] <- cost, next
                    for n in neighbor do
                        let p, c = n
                        let route = p :: next
                        push route (c + cost) note
                    loop exprored  note
                else
                    loop exprored  note
    
    loop exprored Collection
