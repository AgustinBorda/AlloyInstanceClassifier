sig Element {}

one sig Array {
  // Maps indexes to elements of Element.
  i2e: Int -> lone Element,
  // Represents the length of the array.
  length: Int
}

// Assume all elements are in the array.
fact Reachable {
  Element = Array.i2e[Int]
}

fact InBound {
  // All indexes should be greater than or equal to 0 and less than the array length.
  all i: Int | (i >= 0 and i < Array.length) implies (some Array.i2e[i])
  // Array length should be greater than or equal to 0.
  Array.length >= 0
}

pred NoConflict() {
  // Each index maps to at most one element.
  all idx: Int | lone Array.i2e[idx]
}



assert repair_assert_1 {
  NoConflict
  all i: Int | (i >= 0 and i < Array.length) implies (some Array.i2e[i])
}



pred repair_pred_1 {
  NoConflict
  all i: Int | (i >= 0 and i < Array.length) implies (some Array.i2e[i])
}

