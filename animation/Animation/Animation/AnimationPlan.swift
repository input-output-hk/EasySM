import Foundation

// MARK: - Animation steps

/// A single step in an animation plan.
enum AnimationStep: Equatable, Codable {
  /// Transition to a state (node) and display an associated value.
  /// - Parameters:
  ///   - node: The id of the target node.
  ///   - valueText: The associated value to display on the node (e.g. `"∅"` or a tuple string).
  case state(node: String, valueText: String?)

  /// Traverse an edge, showing a moving token with a label and optional value.
  /// - Parameters:
  ///   - edge: The id of the edge to animate along.
  ///   - label: Short label shown on the moving token.
  ///   - valueText: Optional value shown beneath the token label.
  case action(edge: String, label: String, valueText: String?)

  private enum CodingKeys: String, CodingKey {
    case type, node, edge, label, valueText
  }

  private enum StepType: String, Codable {
    case state, action
  }

  init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    let type = try container.decode(StepType.self, forKey: .type)
    switch type {
    case .state:
      let node = try container.decode(String.self, forKey: .node)
      let valueText = try container.decodeIfPresent(String.self, forKey: .valueText)
      self = .state(node: node, valueText: valueText)
    case .action:
      let edge = try container.decode(String.self, forKey: .edge)
      let label = try container.decode(String.self, forKey: .label)
      let valueText = try container.decodeIfPresent(String.self, forKey: .valueText)
      self = .action(edge: edge, label: label, valueText: valueText)
    }
  }

  func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    switch self {
    case .state(let node, let valueText):
      try container.encode(StepType.state, forKey: .type)
      try container.encode(node, forKey: .node)
      try container.encodeIfPresent(valueText, forKey: .valueText)
    case .action(let edge, let label, let valueText):
      try container.encode(StepType.action, forKey: .type)
      try container.encode(edge, forKey: .edge)
      try container.encode(label, forKey: .label)
      try container.encodeIfPresent(valueText, forKey: .valueText)
    }
  }
}

// MARK: - Animation plan

/// A sequence of steps that drives an automaton animation.
struct AnimationPlan: Equatable, Codable {
  /// The node id of the initial state (before any steps run).
  let initialState: String
  /// The associated value displayed on the initial state.
  let initialValue: String?
  /// The ordered steps to animate.
  let steps: [AnimationStep]
}
