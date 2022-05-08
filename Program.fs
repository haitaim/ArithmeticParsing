open System
open System.Collections.Immutable
open System.Linq

let abort message =
    eprintfn "%s" message
    System.Environment.Exit 1

type Number =
    { Lexeme: string;
      Value: float }

type ArithmeticToken =
    | RightParenthesis
    | LeftParenthesis
    | Addition
    | Subtraction
    | Multiplication
    | Division
    | Negation
    | Exponentiation
    | NumberToken of Number

let tokenizeInput input =
    let determineMinus lastToken =
        match lastToken with
        | NumberToken(_) | RightParenthesis -> Subtraction
        | _ -> Negation

    let rec getNumber number state =
        match state with
        | n :: tail when n >= '0' && n <= '9' ->
            getNumber (number + string n) tail
        | '.' :: _ when Seq.contains '.' number ->
            abort "Improper number"
            number, state
        | '.' :: tail -> getNumber (number + ".") tail
        | _ -> number, state

    let rec loop (tokens: ImmutableList<ArithmeticToken>) characters =
        match characters with
        | [] -> tokens
        | head :: tail ->
            match head with
            | ' ' | '\t' -> loop tokens tail
            | '(' -> loop (tokens.Add(LeftParenthesis)) tail
            | ')' -> loop (tokens.Add(RightParenthesis)) tail
            | '+' -> loop (tokens.Add(Addition)) tail
            | '*' -> loop (tokens.Add(Multiplication)) tail
            | '/' -> loop (tokens.Add(Division)) tail
            | '^' -> loop (tokens.Add(Exponentiation)) tail
            | '-' ->
                let token = tokens.LastOrDefault(LeftParenthesis) |> determineMinus
                loop (tokens.Add(token)) tail
            | n when (n >= '0' && n <= '9') ->
                let number, newState = getNumber (string n) tail
                let token =
                    { Lexeme = number; Value = float number }
                    |> NumberToken
                loop (tokens.Add(token)) newState
            | unknown ->
                unknown |> sprintf "Unknown character encountered: %c" |> abort
                tokens

    input
        |> Seq.toList
        |> loop ImmutableList<ArithmeticToken>.Empty
        |> Seq.toList

let shuntingYard input =
    let operatorPrecedence operator =
        match operator with
        | Addition | Subtraction -> 1
        | Multiplication | Division -> 2
        | Negation -> 3
        | Exponentiation -> 4
        | _ ->
            operator
                |> sprintf "Program error: %A in operatorPrecedence function"
                |> abort
            0

    let rec operatorLoop op (output: ImmutableList<ArithmeticToken>) opStack =
        match opStack with
        | RightParenthesis :: _ | NumberToken(_) :: _ ->
            opStack.Head
                |> sprintf "Program error: %A in opStack during operatorLoop function"
                |> abort
            output, opStack
        | LeftParenthesis :: _ | [] -> output, (op :: opStack)
        | Exponentiation :: _ when op = Exponentiation ->
            output, (op :: opStack)
        | stackTop :: tail when operatorPrecedence stackTop >= operatorPrecedence op ->
            operatorLoop op (output.Add(stackTop)) tail
        | _ -> output, (op :: opStack)

    let rec parenthesisLoop (output: ImmutableList<ArithmeticToken>) opStack =
        match opStack with
        | LeftParenthesis :: tail -> output, tail
        | head :: tail -> parenthesisLoop (output.Add(head)) tail
        | [] ->
            abort "Mismatched parenthesis"
            output, opStack

    let rec loop tokens (output: ImmutableList<ArithmeticToken>) opStack =
        match tokens with
        | [] -> output, opStack
        | head :: tail ->
            match head with
            | NumberToken(_) -> loop tail (output.Add(tokens.Head)) opStack
            | LeftParenthesis -> loop tail output (tokens.Head :: opStack)
            | RightParenthesis -> parenthesisLoop output opStack ||> loop tail
            | _ -> operatorLoop head output opStack ||> loop tail

    let rec clearOpStack (output: ImmutableList<ArithmeticToken>) opStack =
        match opStack with
        | [] -> output
        | LeftParenthesis :: _ ->
            abort "Mismtached parenthesis"
            output
        | head :: tail -> clearOpStack (output.Add(head)) tail

    loop input ImmutableList<ArithmeticToken>.Empty []
        ||> clearOpStack
        |> Seq.toList

type UnaryOp =
    { Lexeme: char;
      Operation: (float -> float) }

type BinaryOp =
    { Lexeme: char;
      Operation: (float -> float -> float) }

type ExpressionTree =
    | Leaf of Number
    | UnaryNode of UnaryOp * ExpressionTree
    | BinaryNode of BinaryOp * ExpressionTree * ExpressionTree

let constructTree input =
    let constructBinaryExpr stack lexeme op =
        let extractLeaves stack =
            match stack with
            | top :: next :: tail -> next, top, tail
            | _ ->
                abort "Expression not well formed"
                Leaf({ Lexeme = "0"; Value = 0.0 }), Leaf({ Lexeme = "0"; Value = 0.0 }), stack

        let firstExpr, secondExpr, stackTop = extractLeaves stack

        let newExpression =
            BinaryNode({ Lexeme = lexeme; Operation = op }, firstExpr, secondExpr)

        newExpression :: stackTop

    let rec loop tokens stack =
        match tokens with
        | NumberToken(n) :: tail -> loop tail (Leaf(n) :: stack)
        | Addition :: tail -> loop tail (constructBinaryExpr stack '+' (+))
        | Subtraction :: tail -> loop tail (constructBinaryExpr stack '-' (-))
        | Multiplication :: tail -> loop tail (constructBinaryExpr stack '*' (*))
        | Division :: tail -> loop tail (constructBinaryExpr stack '/' (/))
        | Exponentiation :: tail -> loop tail (constructBinaryExpr stack '^' ( ** ))
        | Negation :: tail ->
            let expression, stackTop =
                match stack with
                | expression :: stackTop -> expression, stackTop
                | [] ->
                    abort "Program error"
                    stack.Head, stack

            let newExpression =
                UnaryNode(
                    { Lexeme = '-'; Operation = (-) 0.0 },
                    expression
                )
            loop tail (newExpression :: stackTop)
        | [] when stack.Length = 1 -> stack.Head
        | _ ->
            abort "Expression not well formed"
            stack.Head

    loop input []

let rec evaluateTree tree =
    match tree with
    | Leaf(n) -> n.Value
    | UnaryNode(op, node) -> op.Operation (evaluateTree node)
    | BinaryNode(op, left, right) -> op.Operation (evaluateTree left) (evaluateTree right)

let printInfix tree =
    let rec traverse t =
        match t with
        | Leaf(n) -> sprintf " %f" n.Value
        | UnaryNode(op, node) -> sprintf " %c%s" op.Lexeme (traverse node)
        | BinaryNode(op, left, right) ->
            sprintf "(%s %c%s)" (traverse left) op.Lexeme (traverse right)

    printfn "%s" (traverse tree)

let printPostfix tree =
    let rec traverse t =
        match t with
        | Leaf(n) -> sprintf " %f" n.Value
        | UnaryNode(op, node) -> sprintf "%s %c" (traverse node) op.Lexeme
        | BinaryNode(op, left, right) ->
            sprintf "%s%s %c" (traverse left) (traverse right) op.Lexeme

    printfn "%s" (traverse tree)

let printPrefix tree =
    let rec traverse t =
        match t with
        | Leaf(n) -> sprintf " %f" n.Value
        | UnaryNode(op, node) -> sprintf " %c%s" op.Lexeme (traverse node)
        | BinaryNode(op, left, right) ->
            sprintf " %c%s%s" op.Lexeme (traverse left) (traverse right)

    printfn "%s" (traverse tree)

let rec interactWithTree tree =
    printf "\n> "
    match System.Console.ReadLine () with
    | "1" ->
        printInfix tree
        interactWithTree tree
    | "2" ->
        printPostfix tree
        interactWithTree tree
    | "3" ->
        printPrefix tree
        interactWithTree tree
    | "4" ->
        printfn "The expression evaluated to: %f" (evaluateTree tree)
        interactWithTree tree
    | "5" -> ()
    | _ ->
        printfn "Invalid input"
        interactWithTree tree

[<EntryPoint>]
let main argv =
    printf "Write an arithmetic expression: "
    let tree =
        System.Console.ReadLine ()
        |> tokenizeInput
        |> shuntingYard
        |> constructTree

    let prompt =
        """
1) Print Infix
2) Print Postfix
3) Print Prefix
4) Evaluate
5) Quit
"""

    printf "%s" prompt
    interactWithTree tree
    0

