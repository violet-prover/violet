type t = { mutable events : Violet_elab.Observer.event list }

let create () = { events = [] }
let on_event t ev = t.events <- ev :: t.events
let to_index t = Index.of_events t.events
