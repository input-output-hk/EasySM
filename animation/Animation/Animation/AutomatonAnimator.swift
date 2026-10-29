import SwiftUI

// MARK: - Geometry helpers

/// Point on a cubic Bezier curve at parameter t ∈ [0,1].
func bezierPoint(_ b: BezierCurve, _ t: CGFloat) -> CGPoint {
  let mt = 1 - t
  let a = mt * mt * mt, bq = 3 * mt * mt * t
  let c = 3 * mt * t * t, d = t * t * t
  return CGPoint(x: a * b.p0.x + bq * b.c1.x + c * b.c2.x + d * b.p1.x,
                 y: a * b.p0.y + bq * b.c1.y + c * b.c2.y + d * b.p1.y)
}

/// Tangent vector on a cubic Bezier curve at parameter t ∈ [0,1] (for arrowhead direction).
func bezierTangent(_ b: BezierCurve, _ t: CGFloat) -> CGVector {
  let mt = 1 - t
  let x = 3 * mt * mt * (b.c1.x - b.p0.x) + 6 * mt * t * (b.c2.x - b.c1.x) + 3 * t * t * (b.p1.x - b.c2.x)
  let y = 3 * mt * mt * (b.c1.y - b.p0.y) + 6 * mt * t * (b.c2.y - b.c1.y) + 3 * t * t * (b.p1.y - b.c2.y)
  return CGVector(dx: x, dy: y)
}

// MARK: - Moving token (label + value travel along an edge)

struct MovingToken: Identifiable {
  let id = UUID()
  let label: String
  let valueText: String?
  let bezier: BezierCurve

  static let duration: TimeInterval = 1.6
}

struct TokenView: View {
  let token: MovingToken
  @State private var startDate = Date()

  var body: some View {
    TimelineView(.periodic(from: startDate, by: 1/60)) { context in
      let elapsed = context.date.timeIntervalSince(startDate)
      let t = min(1, CGFloat(elapsed) / MovingToken.duration)
      let progress = t * t * (3 - 2 * t) // ease-in-out smoothstep
      let pos = bezierPoint(token.bezier, progress)

      VStack(spacing: 2) {
        Text(token.label)
          .font(.system(size: 13, weight: .semibold, design: .monospaced))
          .padding(.horizontal, 8).padding(.vertical, 3)
          .background(Capsule().fill(Color.accentColor))
          .foregroundStyle(.white)
        if let value = token.valueText {
          Text(value)
            .font(.system(size: 11, design: .monospaced))
            .padding(.horizontal, 6).padding(.vertical, 2)
            .background(Capsule().fill(Color(nsColor: .controlBackgroundColor)))
            .overlay(Capsule().strokeBorder(Color.accentColor.opacity(0.6), lineWidth: 1))
        }
      }
      .position(pos)
    }
  }
}

// MARK: - State node with associated value

struct StateNode: View {
  let name: String
  let valueText: String?
  let size: CGSize

  var body: some View {
    VStack(spacing: 8) {
      Text(name)
        .font(.system(size: 20, weight: .bold, design: .rounded))
      ZStack {
        // Invisible placeholder keeps the layout stable when no value is shown.
        Text("∅")
          .font(.system(size: 13, design: .monospaced))
          .opacity(0)
        if let value = valueText {
          Text(value)
            .font(.system(size: 13, design: .monospaced))
            .id(value) // Identity change triggers the overflow transition.
            .transition(.asymmetric(
              insertion: .move(edge: .top).combined(with: .opacity),
              removal:   .move(edge: .bottom).combined(with: .opacity)))
        }
      }
      .frame(minWidth: 120)
      .padding(.horizontal, 10).padding(.vertical, 5)
      .background(RoundedRectangle(cornerRadius: 6).fill(Color(nsColor: .controlBackgroundColor)))
      .overlay(RoundedRectangle(cornerRadius: 6).strokeBorder(Color(nsColor: .separatorColor)))
    }
    .padding(18)
    .frame(width: size.width, height: size.height)
    .background(
      RoundedRectangle(cornerRadius: 16)
        .fill(Color(nsColor: .windowBackgroundColor))
        .shadow(color: .black.opacity(0.15), radius: 6, y: 3)
    )
    .overlay(
      RoundedRectangle(cornerRadius: 16)
        .strokeBorder(valueText != nil ? Color.accentColor : Color(nsColor: .separatorColor),
                      lineWidth: valueText != nil ? 2.5 : 1.5)
    )
  }
}

// MARK: - Arrowhead

struct ArrowHead: Shape {
  let bezier: BezierCurve

  func path(in rect: CGRect) -> Path {
    let t: CGFloat = 0.97
    let tip = bezierPoint(bezier, 1)
    let back = bezierPoint(bezier, t)
    let v = bezierTangent(bezier, t)
    let angle = atan2(v.dy, v.dx)
    let size: CGFloat = 12

    var p = Path()
    p.move(to: tip)
    p.addLine(to: CGPoint(x: back.x + cos(angle + .pi / 2) * size * 0.4,
                          y: back.y + sin(angle + .pi / 2) * size * 0.4))
    p.addLine(to: CGPoint(x: back.x + cos(angle - .pi / 2) * size * 0.4,
                          y: back.y + sin(angle - .pi / 2) * size * 0.4))
    p.closeSubpath()
    return p
  }
}

// MARK: - Automaton animator

/// A generalized view that animates any augmented automaton from an
/// `AutomatonConfiguration` (structure + layout) and an `AnimationPlan` (sequence).
struct AutomatonAnimator: View {
  let configuration: AutomatonConfiguration
  let plan: AnimationPlan
  let runID: Int

  @State private var currentNode: String
  @State private var currentValue: String?
  @State private var tokens: [MovingToken] = []
  @State private var runTask: Task<Void, Never>?

  init(configuration: AutomatonConfiguration, plan: AnimationPlan, runID: Int) {
    self.configuration = configuration
    self.plan = plan
    self.runID = runID
    _currentNode = State(initialValue: plan.initialState)
    _currentValue = State(initialValue: plan.initialValue)
  }

  var body: some View {
    GeometryReader { geo in
      let scale = min(geo.size.width / configuration.designSize.width,
                      geo.size.height / configuration.designSize.height)
      ZStack {
        edgesLayer
        nodesLayer
        ForEach(tokens) { TokenView(token: $0) }
      }
      .frame(width: configuration.designSize.width, height: configuration.designSize.height)
      .scaleEffect(scale, anchor: .center)
      .frame(width: geo.size.width, height: geo.size.height)
    }
    .onChange(of: runID) { _, _ in
      restart()
    }
    .onDisappear { runTask?.cancel() }
  }

  // MARK: Edges

  private var edgesLayer: some View {
    ForEach(configuration.edges) { edge in
      let b = edge.bezier
      Path { p in
        p.move(to: b.p0)
        p.addCurve(to: b.p1, control1: b.c1, control2: b.c2)
      }
      .stroke(Color(nsColor: .separatorColor), lineWidth: 2)

      // Arrowhead at the end of the curve.
      ArrowHead(bezier: b)
        .fill(Color(nsColor: .separatorColor))

      // Static edge label.
      Text(edge.label)
        .font(.system(size: 13, design: .monospaced))
        .position(bezierPoint(b, edge.labelPosition.t))
        .offset(edge.labelPosition.offset)
    }
  }

  // MARK: Nodes

  private var nodesLayer: some View {
    ForEach(configuration.nodes) { node in
      StateNode(
        name: node.name,
        valueText: node.id == currentNode ? currentValue : nil,
        size: configuration.nodeSize
      )
      .position(configuration.pixelPosition(for: node.gridPosition))
    }
  }

  // MARK: Sequence runner

  func restart() {
    runTask?.cancel()
    tokens.removeAll()
    currentNode = plan.initialState
    currentValue = plan.initialValue
    runTask = Task { @MainActor in
      try? await Task.sleep(for: .seconds(0.4))
      for step in plan.steps {
        if Task.isCancelled { return }
        switch step {
        case .state(let node, let valueText):
          withAnimation(.spring(response: 0.6, dampingFraction: 0.8)) {
            currentNode = node
            currentValue = valueText
          }
          try? await Task.sleep(for: .seconds(1.0))
        case .action(let edgeId, let label, let valueText):
          guard let edge = configuration.edge(id: edgeId) else { continue }
          let token = MovingToken(label: label, valueText: valueText, bezier: edge.bezier)
          withAnimation(.easeOut(duration: 0.25)) {
            tokens.append(token)
          }
          try? await Task.sleep(for: .seconds(MovingToken.duration))
          withAnimation(.easeIn(duration: 0.25)) {
            tokens.removeAll { $0.id == token.id }
          }
          try? await Task.sleep(for: .seconds(0.35))
        }
      }
    }
  }
}
