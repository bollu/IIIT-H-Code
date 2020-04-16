module MergeSort1 exposing (main, init, update, view)
import Browser
import Html exposing (Html, Attribute, div, input, button, text)
import Html.Attributes exposing (type_, value, style, disabled)
import Html.Events exposing (onInput, onClick)
import Array exposing (Array)



-- MAIN
main: Program () Model Msg
main = 
  Browser.sandbox {init = init, update = update, view = view}



-- MODEL
type alias Model = {
    a: Array Int,
    i: Int,
    j: Int
  }

init: Model
init =
  Model initArray -1 -1

initArray: Array Int
initArray =
  Array.fromList [7, 5, 9, 4, 2, 1, 8]



-- UPDATE
type Msg =
  Change Int String |
  Pick Int |
  Swap

update: Msg -> Model -> Model
update msg model =
  case msg of
    Change k s ->
      {model | a = Array.set k (toInt s) model.a}
    Pick k ->
      if k == model.i then
        {model | i = -1}
      else if k == model.j then
        {model | j = -1}
      else if model.i == -1 then
        {model | i = k}
      else
        {model | j = k}
    Swap ->
      if model.i >=0 && model.j >=0 then
        {model | a = arraySwap 0 model.i model.j model.a, i = -1, j = -1}
      else
        model



-- VIEW
view: Model -> Html Msg
view model =
  div styleBody [
    div [] (Array.toList (Array.indexedMap
      (\i v -> viewNum v (Change i) (Pick i) (i==model.i || i==model.j))
      model.a
    )),
    div styleSubmit [
      viewBtn (model.i<0 || model.j<0) Swap
    ]
  ]

viewNum: Int -> (String -> msg) -> msg -> Bool -> Html msg
viewNum v inp clk h =
  input (styleNum h ++ [
    type_ "number",
    value (String.fromInt v),
    onInput inp,
    onClick clk
  ]) []

viewBtn: Bool -> msg -> Html msg
viewBtn d msg =
  button (styleBtn ++ [
    disabled d,
    onClick msg
  ]) [text "Swap"]



-- STYLES
styleNum: Bool -> List (Attribute m)
styleNum h = [
    style "border-bottom" (if h then "3px solid green" else ""),
    style "font-size" "1.5em",
    style "width" "3em"
  ]

styleBody: List (Attribute m)
styleBody = [
    style "text-align" "center",
    style "margin" "2em"
  ]

styleSubmit: List (Attribute m)
styleSubmit = [
    style "margin-top" "1em"
  ]

styleBtn: List (Attribute m)
styleBtn = [
    style "font-size" "1.5em"
  ]



-- UTIL
toInt: String -> Int
toInt s =
  Maybe.withDefault 0 (String.toInt s)

arraySwap: a -> Int -> Int -> Array a -> Array a
arraySwap d i j x =
  let a = Maybe.withDefault d (Array.get i x)
      b = Maybe.withDefault d (Array.get j x)
  in Array.set i b (Array.set j a x)
