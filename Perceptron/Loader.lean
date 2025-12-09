import Perceptron.Definitions

/-- Parse an integer from string, return as ℚ -/
def parseIntAsRat (s : String) : Option ℚ :=
  let s := s.trim
  if s.isEmpty then none
  else
    match s.toList with
    | '-' :: rest => (String.ofList rest).toNat?.map fun n => (-(n : Int) : ℚ)
    | _ => s.toNat?.map fun n => ((n : Int) : ℚ)

/-- Parse a line of CSV into features and label -/
def parseCSVLine (line : String) : Option (List ℚ × ℚ) := do
  let parts := line.splitOn ","
  match parts with
  | label :: features => do
      let fs ← features.mapM parseIntAsRat
      let lab ← parseIntAsRat label
      return (fs, lab)
  | [] => none

/-- Convert list of rationals to Fin n → ℚ -/
def listToFin (lst : List ℚ) (n : Nat) (h : lst.length = n) : Fin n → ℚ :=
  fun i => lst.get ⟨i.val, by rw [h]; exact i.isLt⟩

/-- Parse all data lines into a dataset -/
def parseDataLines (lines : List String) (nFeatures : Nat) : List (DataPoint nFeatures) :=
  lines.filterMap fun line =>
    if line.trim.isEmpty then none
    else
      parseCSVLine line |>.bind fun (features, label) =>
        if h : features.length = nFeatures then
          some { features := listToFin features nFeatures h, label := label }
        else none

/-- Load a CSV dataset file into Dataset n -/
def loadCSVDataset (path : System.FilePath) (nFeatures : Nat) : IO (Σ n, Dataset n) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n" |>.filter (·.trim.length > 0)
  let dataset := parseDataLines lines nFeatures
  -- IO.println s!"Loaded {dataset.length} samples"
  return ⟨nFeatures, dataset⟩

-- Visualization

/-- Convert a rational to a block character based on threshold -/
def toBlock (x : ℚ) (thresh : ℚ := 0) : String :=
  if x > thresh then "█" else " "

/-- Convert a vector to a string of blocks -/
def vectorToBlocks {n : Nat} (v : Fin n → ℚ) (thresh : ℚ := 0) : String :=
  (List.finRange n).map (fun i => toBlock (v i) thresh) |> String.join

/-- Convert a vector to blocks with a given width (inserts newlines) -/
def vectorToBlocksGrid {n : Nat} (v : Fin n → ℚ) (width : Nat) (thresh : ℚ := 0) : String :=
  let blocks := (List.finRange n).map (fun i => toBlock (v i) thresh)
  let rows := blocks.toChunks width |>.map String.join
  String.intercalate "\n" rows

/-- Visualize a data point -/
def showDataPoint {n : Nat} (dp : DataPoint n) (width : Nat := 0) (thresh : ℚ := 0) : String :=
  let grid := if width > 0
    then vectorToBlocksGrid dp.features width thresh
    else vectorToBlocks dp.features thresh
  s!"Label: {dp.label}\n{grid}"

/-- Print a data point -/
def printDataPoint {n : Nat} (dp : DataPoint n) (width : Nat := 0) (thresh : ℚ := 0) : IO Unit :=
  IO.println (showDataPoint dp width thresh)

def loadSamples
  (path : String) (samples : Nat := 3) (width : Nat := 28) (thresh : ℚ := 0) : IO Unit := do
  let ⟨_, data⟩ ← loadCSVDataset path 784
  let samples := data.take samples
  samples.forM (fun dp => printDataPoint dp width thresh)

-- Sample usage
#eval loadSamples "mnist_pruned.csv" 3 28 170
