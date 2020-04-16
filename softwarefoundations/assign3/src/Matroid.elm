module Matroid exposing (main, init, update, view)
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
-- find number x such that x < smallthan, x > 
type Model = Model 
  { arr: Array Int
  , smallerthan: Int
  , bestix: Int
  , curix: Int,
  , matroidarr: Array Bool
  , basesSets: Array (Array Bool) -- contains the bases: smallest independent sets
  }

init: Model
init = Sorting { a = initArray, smallerthan = 1000, bestix = 0, curix = 0}

initArray: Array Int
initArray =
  Array.fromList [7, 5, 9, 4, 2, 1, 8]



-- UPDATE
type Msg =
  Change Int String |
  Pick Int |
  Swap

update: Msg -> Model -> Model
update msg model = model



-- VIEW
view: Model -> Html Msg
view model =
  div styleBody [
    div styleSubmit [
      viewBtn  True Swap
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
