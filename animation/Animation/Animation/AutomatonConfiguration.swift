import SwiftUI

// MARK: - Codable helpers for CoreGraphics types

/// A Codable wrapper for CGPoint, encoded as {"x": …, "y": …}.
struct CodablePoint: Codable, Equatable {
  let x: CGFloat
  let y: CGFloat

  init(_ point: CGPoint) {
    self.x = point.x
    self.y = point.y
  }

  var point: CGPoint { CGPoint(x: x, y: y) }
}

/// A Codable wrapper for CGSize, encoded as {"width": …, "height": …}.
struct CodableSize: Codable, Equatable {
  let width: CGFloat
  let height: CGFloat

  init(_ size: CGSize) {
    self.width = size.width
    self.height = size.height
  }

  var size: CGSize { CGSize(width: width, height: height) }
}

// MARK: - Grid layout

/// A position on the automaton's layout grid (zero-indexed).
struct GridPosition: Hashable, Equatable, Codable {
  let row: Int
  let column: Int
}

// MARK: - Automaton nodes

/// A state node in the automaton, placed on a grid cell.
struct AutomatonNode: Identifiable, Equatable, Codable {
  /// Unique identifier for the node (also serves as the state key).
  let id: String
  /// Human-readable display name.
  let name: String
  /// Position on the layout grid.
  let gridPosition: GridPosition
}

// MARK: - Bezier curve

/// A cubic Bezier curve defined by four control points in design coordinates.
struct BezierCurve: Equatable, Codable {
  let p0: CGPoint
  let c1: CGPoint
  let c2: CGPoint
  let p1: CGPoint

  enum CodingKeys: String, CodingKey {
    case p0, c1, c2, p1
  }

  init(p0: CGPoint, c1: CGPoint, c2: CGPoint, p1: CGPoint) {
    self.p0 = p0
    self.c1 = c1
    self.c2 = c2
    self.p1 = p1
  }

  init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    p0 = (try container.decode(CodablePoint.self, forKey: .p0)).point
    c1 = (try container.decode(CodablePoint.self, forKey: .c1)).point
    c2 = (try container.decode(CodablePoint.self, forKey: .c2)).point
    p1 = (try container.decode(CodablePoint.self, forKey: .p1)).point
  }

  func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(CodablePoint(p0), forKey: .p0)
    try container.encode(CodablePoint(c1), forKey: .c1)
    try container.encode(CodablePoint(c2), forKey: .c2)
    try container.encode(CodablePoint(p1), forKey: .p1)
  }
}

// MARK: - Label placement

/// Where to place a label along a curve: at parameter t with a pixel offset.
struct LabelPlacement: Equatable, Codable {
  /// Position along the curve, t ∈ [0,1].
  let t: CGFloat
  /// Pixel offset from the curve point.
  let offset: CGSize

  enum CodingKeys: String, CodingKey {
    case t, offset
  }

  init(t: CGFloat, offset: CGSize) {
    self.t = t
    self.offset = offset
  }

  init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    t = try container.decode(CGFloat.self, forKey: .t)
    offset = (try container.decode(CodableSize.self, forKey: .offset)).size
  }

  func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(t, forKey: .t)
    try container.encode(CodableSize(offset), forKey: .offset)
  }
}

// MARK: - Automaton edges

/// A labelled, directed edge between two nodes.
struct AutomatonEdge: Identifiable, Equatable, Codable {
  /// Unique identifier for the edge (used to reference it in an animation plan).
  let id: String
  /// Static label displayed on the edge.
  let label: String
  /// Source node id.
  let source: String
  /// Target node id.
  let target: String
  /// Cubic Bezier curve in design coordinates.
  let bezier: BezierCurve
  /// Position of the static label along the curve.
  let labelPosition: LabelPlacement
}

// MARK: - Automaton configuration

/// Complete configuration for an augmented automaton: nodes placed on a grid,
/// with labelled edges (including bezier curves) between them.
struct AutomatonConfiguration: Equatable, Codable {
  /// Human-readable name of the contract being visualised.
  let contractName: String
  let nodes: [AutomatonNode]
  let edges: [AutomatonEdge]
  /// The design-space dimensions used for scaling.
  let designSize: CGSize
  /// Number of rows in the layout grid.
  let gridRows: Int
  /// Number of columns in the layout grid.
  let gridColumns: Int
  /// Size of each node view.
  let nodeSize: CGSize

  enum CodingKeys: String, CodingKey {
    case contractName, nodes, edges, designSize, gridRows, gridColumns, nodeSize
  }

  init(
    contractName: String,
    nodes: [AutomatonNode],
    edges: [AutomatonEdge],
    designSize: CGSize,
    gridRows: Int,
    gridColumns: Int,
    nodeSize: CGSize
  ) {
    self.contractName = contractName
    self.nodes = nodes
    self.edges = edges
    self.designSize = designSize
    self.gridRows = gridRows
    self.gridColumns = gridColumns
    self.nodeSize = nodeSize
  }

  init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    contractName = try container.decode(String.self, forKey: .contractName)
    nodes = try container.decode([AutomatonNode].self, forKey: .nodes)
    edges = try container.decode([AutomatonEdge].self, forKey: .edges)
    designSize = (try container.decode(CodableSize.self, forKey: .designSize)).size
    gridRows = try container.decode(Int.self, forKey: .gridRows)
    gridColumns = try container.decode(Int.self, forKey: .gridColumns)
    nodeSize = (try container.decode(CodableSize.self, forKey: .nodeSize)).size
  }

  func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(contractName, forKey: .contractName)
    try container.encode(nodes, forKey: .nodes)
    try container.encode(edges, forKey: .edges)
    try container.encode(CodableSize(designSize), forKey: .designSize)
    try container.encode(gridRows, forKey: .gridRows)
    try container.encode(gridColumns, forKey: .gridColumns)
    try container.encode(CodableSize(nodeSize), forKey: .nodeSize)
  }

  /// Compute the pixel position (centre) of a grid cell in design coordinates.
  func pixelPosition(for position: GridPosition) -> CGPoint {
    let cellWidth = designSize.width / CGFloat(gridColumns)
    let cellHeight = designSize.height / CGFloat(gridRows)
    return CGPoint(
      x: (CGFloat(position.column) + 0.5) * cellWidth,
      y: (CGFloat(position.row) + 0.5) * cellHeight
    )
  }

  /// Look up a node by id.
  func node(id: String) -> AutomatonNode? {
    nodes.first { $0.id == id }
  }

  /// Look up an edge by id.
  func edge(id: String) -> AutomatonEdge? {
    edges.first { $0.id == id }
  }
}
