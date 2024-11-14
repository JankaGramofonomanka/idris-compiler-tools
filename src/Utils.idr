module Utils

||| Make the implicit implementation of an interface explicit.
|||
||| The name follows a convention from Scala
||| @ ifc  the interface
||| @ impl the implementation
export
implicitly : (impl : ifc) => ifc
implicitly {impl} = impl
