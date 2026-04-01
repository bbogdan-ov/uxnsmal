package uxnsmal

Symbol :: union #no_nil {
	Symbol_Func,
	Symbol_Var,
	Symbol_Const,
	Symbol_Data,
	Symbol_User_Type,
}

Symbol_Func :: struct #all_or_none {
	id:         ID,
	name:       Name,
	signature:  Signature,
	defined_at: Span,
}
Symbol_Var :: struct #all_or_none {
	id:         ID,
	name:       Name,
	type:       Type,
	defined_at: Span,
}
Symbol_Const :: struct #all_or_none {
	id:         ID,
	name:       Name,
	type:       Type,
	defined_at: Span,
}
Symbol_Data :: struct #all_or_none {
	id:         ID,
	name:       Name,
	defined_at: Span,
}

Symbol_User_Type :: union #no_nil {
	User_Type_Alias,
	User_Type_Enum,
	User_Type_Struct,
}
User_Type_Alias :: struct #all_or_none {
	id:         ID,
	name:       Name,
	derived:    Type,
	defined_at: Span,
}
User_Type_Enum :: struct #all_or_none {
	id:         ID,
	name:       Name,
	derived:    Type,
	variants:   map[string]Span,
	defined_at: Span,
}
User_Type_Struct :: struct #all_or_none {
	id:         ID,
	name:       Name,
	fields:     map[string]Struct_Field,
	defined_at: Span,
}
Struct_Field :: struct #all_or_none {
	type: Type,
	span: Span,
}

symbol_name :: proc(s: Symbol) -> Name {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return sym.name
	case Symbol_Var:   return sym.name
	case Symbol_Const: return sym.name
	case Symbol_Data:  return sym.name
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return ty.name
		case User_Type_Enum:   return ty.name
		case User_Type_Struct: return ty.name
		}
	}
	// odinfmt: enable

	unreachable()
}
symbol_kind_str :: proc(s: Symbol) -> string {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return "function"
	case Symbol_Var:   return "variable"
	case Symbol_Const: return "constant"
	case Symbol_Data:  return "data"
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return "user type"
		case User_Type_Enum:   return "enum"
		case User_Type_Struct: return "struct"
		}
	}
	// odinfmt: enable

	unreachable()
}
symbol_defined_at :: proc(s: Symbol) -> Span {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return sym.defined_at
	case Symbol_Var:   return sym.defined_at
	case Symbol_Const: return sym.defined_at
	case Symbol_Data:  return sym.defined_at
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return ty.defined_at
		case User_Type_Enum:   return ty.defined_at
		case User_Type_Struct: return ty.defined_at
		}
	}
	// odinfmt: enable

	unreachable()
}
