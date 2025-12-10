import Perceptron.Definitions
import Perceptron.Basic

/-- Parse an integer from string, return as ℚ -/
def parse_rat (s : String) : Option ℚ :=
  let s := s.trim
  if s.isEmpty then none
  else
    match s.toList with
    | '-' :: rest => (String.ofList rest).toNat?.map fun n => (-(n : Int) : ℚ)
    | _ => s.toNat?.map fun n => ((n : Int) : ℚ)

/-- Parse a line of CSV into features and label -/
def parse_csv_line (line : String) : Option (List ℚ × ℚ) := do
  let parts := line.splitOn ","
  match parts with
  | label :: features => do
      let fs ← features.mapM parse_rat
      let lab ← parse_rat label
      return (fs, lab)
  | [] => none

/-- Convert list of rationals to Fin n → ℚ -/
def list_to_fin (lst : List ℚ) (n : Nat) (h : lst.length = n) : Fin n → ℚ :=
  fun i => lst.get ⟨i.val, by rw [h]; exact i.isLt⟩

/-- Parse all data lines into a List (LabeledPoint n) -/
def parse_data_lines (lines : List String) (num_features : Nat) :
  List (LabeledPoint num_features) :=
  lines.filterMap fun line =>
    if line.trim.isEmpty then none
    else
      parse_csv_line line |>.bind fun (features, label) =>
        if h : features.length = num_features then
          some { features := list_to_fin features num_features h, label := label }
        else none

/-- Load a CSV file into List (LabeledPoint n) -/
def load_csv (path : System.FilePath) (num_features : Nat) :
  IO (List (LabeledPoint num_features)) :=
  do
    let contents ← IO.FS.readFile path
    let lines := contents.splitOn "\n" |>.filter (·.trim.length > 0)
    let points := parse_data_lines lines num_features
    return points

-- Visualization

/-- Convert a rational to a block character based on threshold -/
def to_block (x : ℚ) (thresh : ℚ := 0) : String :=
  if x > thresh then "█" else " "

/-- Convert a vector to a string of blocks -/
def vector_to_blocks {n : Nat} (v : Fin n → ℚ) (thresh : ℚ := 0) : String :=
  (List.finRange n).map (fun i => to_block (v i) thresh) |> String.join

/-- Convert a vector to blocks with a given width (inserts newlines) -/
def vector_to_blocks_grid {n : Nat} (v : Fin n → ℚ) (width : Nat) (thresh : ℚ := 0) : String :=
  let blocks := (List.finRange n).map (fun i => to_block (v i) thresh)
  let rows := blocks.toChunks width |>.map String.join
  String.intercalate "\n" rows

/-- Visualize a data point -/
def show_labeled_point {n : Nat}
  (dp : LabeledPoint n) (width : Nat := 0) (thresh : ℚ := 0) : String :=
  let grid := if width > 0
    then vector_to_blocks_grid dp.features width thresh
    else vector_to_blocks dp.features thresh
  s!"Label: {dp.label}\n{grid}"

/-- Print a data point -/
def print_labeled_point {n : Nat}
  (dp : LabeledPoint n) (width : Nat := 0) (thresh : ℚ := 0) : IO Unit :=
  IO.println (show_labeled_point dp width thresh)

def load_samples
  (path : String) (samples : Nat := 3) (width : Nat := 28) (thresh : ℚ := 0) : IO Unit := do
  let data ← load_csv path 784
  let samples := data.take samples
  samples.forM (fun dp => print_labeled_point dp width thresh)

-- Sample usage
#eval load_samples "mnist_pruned.csv" 3 28 170
