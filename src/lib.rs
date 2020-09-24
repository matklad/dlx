use std::{
  cmp::Ordering,
  fmt,
  ops::{self, Range},
};

pub fn solve(mut m: Matrix) -> Vec<Vec<usize>> {
  let mut answers = Vec::new();
  let mut answer = Vec::new();
  go(&mut m, &mut answer, &mut answers);
  answers
}

fn go(
  m: &mut Matrix,
  partial_answer: &mut Vec<Cell>,
  answers: &mut Vec<Vec<usize>>,
) {
  let c = {
    let mut i = m.x.cursor(H);
    let mut c = match i.next(&m.x) {
      Some(it) => it,
      None => {
        let mut answer: Vec<usize> = partial_answer
          .iter()
          .map(|&cell| m.row_of(cell))
          .collect();
        answer.sort();
        answers.push(answer);
        return;
      }
    };
    while let Some(next_c) = i.next(&m.x) {
      if m.size[next_c] < m.size[c] {
        c = next_c;
      }
    }
    c
  };

  m.cover(c);
  let mut r = m.y.cursor(c);
  while let Some(r) = r.next(&m.y) {
    partial_answer.push(r);
    let mut j = m.x.cursor(r);
    while let Some(j) = j.next(&m.x) {
      m.cover(m.c[j]);
    }
    go(m, partial_answer, answers);
    let mut j = m.x.cursor(r);
    while let Some(j) = j.prev(&m.x) {
      m.uncover(m.c[j]);
    }
    partial_answer.pop();
  }
  m.uncover(c);
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Cell(usize);
const H: Cell = Cell(0);

#[derive(Debug)]
struct Link {
  prev: Cell,
  next: Cell,
}

#[derive(Default, Debug)]
struct LinkedList {
  data: Vec<Link>,
}

impl ops::Index<Cell> for LinkedList {
  type Output = Link;
  fn index(&self, index: Cell) -> &Link {
    &self.data[index.0]
  }
}

impl ops::IndexMut<Cell> for LinkedList {
  fn index_mut(&mut self, index: Cell) -> &mut Link {
    &mut self.data[index.0]
  }
}

impl LinkedList {
  fn with_capacity(cap: usize) -> LinkedList {
    LinkedList { data: Vec::with_capacity(cap) }
  }
  fn alloc(&mut self) -> Cell {
    let cell = Cell(self.data.len());
    self.data.push(Link { prev: cell, next: cell });
    cell
  }
  /// Inserts `b` into `a <-> c` to get `a <-> b <-> c`
  fn insert(&mut self, a: Cell, b: Cell) {
    let c = self[a].next;

    self[b].prev = a;
    self[b].next = c;

    self[a].next = b;
    self[c].prev = b;
  }
  /// Removes `b` from `a <-> b <-> c` to get `a <-> c`
  fn remove(&mut self, b: Cell) {
    let a = self[b].prev;
    let c = self[b].next;

    self[a].next = self[b].next;
    self[c].prev = self[b].prev;
  }
  /// Restores previously removed `b` to get `a <-> b <-> c`
  fn restore(&mut self, b: Cell) {
    let a = self[b].prev;
    let c = self[b].next;
    self[a].next = b;
    self[c].prev = b;
  }
  fn cursor(&self, head: Cell) -> Cursor {
    Cursor { head, curr: head }
  }
}

struct Cursor {
  head: Cell,
  curr: Cell,
}

impl Cursor {
  fn next(&mut self, list: &LinkedList) -> Option<Cell> {
    self.curr = list[self.curr].next;
    if self.curr == self.head {
      return None;
    }
    Some(self.curr)
  }
  fn prev(&mut self, list: &LinkedList) -> Option<Cell> {
    self.curr = list[self.curr].prev;
    if self.curr == self.head {
      return None;
    }
    Some(self.curr)
  }
}

#[derive(Debug)]
pub struct Matrix {
  // Auxilary map to get from cell to row, could be encoded more efficiently.
  row_ranges: Vec<Range<Cell>>,
  // SoA fields
  size: Vec<usize>,
  c: Vec<Cell>,
  x: LinkedList,
  y: LinkedList,
}

impl ops::Index<Cell> for Vec<usize> {
  type Output = usize;
  fn index(&self, index: Cell) -> &usize {
    &self[index.0]
  }
}

impl ops::IndexMut<Cell> for Vec<usize> {
  fn index_mut(&mut self, index: Cell) -> &mut usize {
    &mut self[index.0]
  }
}

impl ops::Index<Cell> for Vec<Cell> {
  type Output = Cell;
  fn index(&self, index: Cell) -> &Cell {
    &self[index.0]
  }
}

impl ops::IndexMut<Cell> for Vec<Cell> {
  fn index_mut(&mut self, index: Cell) -> &mut Cell {
    &mut self[index.0]
  }
}

impl Matrix {
  pub fn new(n_cols: usize) -> Matrix {
    let mut res = Matrix {
      row_ranges: Vec::new(),
      size: Vec::with_capacity(n_cols + 1),
      c: Vec::with_capacity(n_cols + 1),
      x: LinkedList::with_capacity(n_cols + 1),
      y: LinkedList::with_capacity(n_cols + 1),
    };
    assert_eq!(res.alloc_column(), H);
    for _ in 0..n_cols {
      res.add_column();
    }
    res
  }
  fn alloc(&mut self, c: Cell) -> Cell {
    self.c.push(c);
    let cell = self.x.alloc();
    assert_eq!(self.y.alloc(), cell);
    cell
  }
  fn alloc_column(&mut self) -> Cell {
    let cell = self.alloc(H);
    self.c[cell] = cell;
    self.size.push(0);
    cell
  }
  fn add_column(&mut self) {
    let new_col = self.alloc_column();
    self.x.insert(self.x[H].prev, new_col);
  }

  pub fn add_row(&mut self, row: &[bool]) {
    assert_eq!(row.len(), self.size.len() - 1);
    let row_start = Cell(self.x.data.len());
    let mut c = H;
    let mut prev = None;
    for &is_filled in row {
      c = self.x[c].next;
      if is_filled {
        self.size[c] += 1;
        let new_cell = self.alloc(c);
        self.y.insert(self.y[c].prev, new_cell);
        if let Some(prev) = prev {
          self.x.insert(prev, new_cell);
        }
        prev = Some(new_cell);
      }
    }
    let row_end = Cell(self.x.data.len());
    self.row_ranges.push(row_start..row_end);
  }

  fn row_of(&self, cell: Cell) -> usize {
    self
      .row_ranges
      .binary_search_by(|range| {
        if cell < range.start {
          Ordering::Greater
        } else if range.start <= cell && cell < range.end {
          Ordering::Equal
        } else {
          Ordering::Less
        }
      })
      .unwrap()
  }

  fn cover(&mut self, c: Cell) {
    self.x.remove(c);
    let mut i = self.y.cursor(c);
    while let Some(i) = i.next(&self.y) {
      let mut j = self.x.cursor(i);
      while let Some(j) = j.next(&self.x) {
        self.y.remove(j);
        self.size[self.c[j]] -= 1;
      }
    }
  }
  fn uncover(&mut self, c: Cell) {
    let mut i = self.y.cursor(c);
    while let Some(i) = i.prev(&self.y) {
      let mut j = self.x.cursor(i);
      while let Some(j) = j.prev(&self.x) {
        self.size[self.c[j]] += 1;
        self.y.restore(j);
      }
    }
    self.x.restore(c);
  }
}

impl fmt::Display for Matrix {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "s: ")?;
    for s in &self.size {
      write!(f, "{:^7}", s)?;
    }
    writeln!(f)?;

    write!(f, "c: ")?;
    for &Cell(c) in &self.c {
      write!(f, "{:^7}", c.saturating_sub(1))?;
    }
    writeln!(f)?;

    write!(f, "x: ")?;
    for link in &self.x.data {
      write!(f, " {:>2}|{:<2} ", link.prev.0, link.next.0)?
    }
    writeln!(f)?;

    write!(f, "y: ")?;
    for link in &self.y.data {
      write!(f, " {:>2}|{:<2} ", link.prev.0, link.next.0)?
    }
    writeln!(f)?;

    write!(f, "i: ")?;
    for i in 0..self.x.data.len() {
      write!(f, "{:^7}", i)?;
    }
    writeln!(f)?;

    Ok(())
  }
}

#[test]
fn smoke() {
  let mut m = Matrix::new(3);
  m.add_row(&[true, false, true]);
  eprintln!("{}", m);
}

#[test]
fn sample_problem() {
  let mut m = Matrix::new(7);
  let f = false;
  let t = true;
  m.add_row(&[f, f, t, f, t, t, f]);
  m.add_row(&[t, f, f, t, f, f, t]);
  m.add_row(&[f, t, t, f, f, t, f]);
  m.add_row(&[t, f, f, t, f, f, f]);
  m.add_row(&[f, t, f, f, f, f, t]);
  m.add_row(&[f, f, f, t, t, f, t]);
  let solutions = solve(m);
  assert_eq!(solutions, vec![vec![0, 3, 4]]);
}

#[test]
fn exhaustive_test() {
  'matrix: for matrix_bits in 0..=0b1111_1111_1111_1111 {
    let mut rows = [0u32; 4];
    for (i, row) in rows.iter_mut().enumerate() {
      *row = (matrix_bits >> (i * 4)) & 0b1111;
      if *row == 0 {
        continue 'matrix;
      }
    }

    let brute_force = {
      let mut n_solutions = 0;
      for mask in 0..=0b1111 {
        let mut or = 0;
        let mut n_ones = 0;
        for (i, &row) in rows.iter().enumerate() {
          if mask & (1 << i) != 0 {
            or |= row;
            n_ones += row.count_ones()
          }
        }
        if or == 0b1111 && n_ones == 4 {
          n_solutions += 1;
        }
      }
      n_solutions
    };

    let dlx = {
      let mut m = Matrix::new(4);
      for row_bits in rows.iter() {
        let mut row = [false; 4];
        for i in 0..4 {
          row[i] = row_bits & (1 << i) != 0;
        }
        m.add_row(&row);
      }
      solve(m).len()
    };
    assert_eq!(brute_force, dlx)
  }
}
