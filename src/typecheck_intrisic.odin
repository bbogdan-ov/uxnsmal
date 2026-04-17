package uxnsmal

@(require_results)
check_expr_intr :: proc(t: ^Typechecker, intr: ^Expr_Intr) -> (err: Error) {
	// TODO: show usage example on error.
	// TODO: "caused by" notes for "not enough operands" errors.
	stack, secondary: ^Stack

	if .Return in intr.modes {
		stack, secondary = &t.rs, &t.ws
	} else {
		stack, secondary = &t.ws, &t.rs
	}

	stack.keep = .Keep in intr.modes
	defer stack.keep = false

	count := len(stack.items)
	sname := stack_name(stack.kind)
	is_short := false

	@(require_results)
	expect_n_values :: proc(s: ^Stack, count: int, span: Span) -> Error {
		if len(s.items) >= count {
			return nil
		}

		return problemf(
			span,
			"expected %d values on the %s stack, but got %s",
			count,
			stack_name(s.kind),
			msg_n_values(len(s.items)),
		)
	}

	@(require_results)
	check_dev_type :: proc(s: ^Stack, dev: Item, span: Span) -> Error {
		_, is_byte := dev.type.(Type_Byte)
		if is_byte do return nil

		MSG :: "device must be a `byte`, but got a `%s` on the %s stack"

		dev_str := type_tprint(dev.type)
		err := problemf(span, MSG, dev_str, stack_name(s.kind))
		problem_notef(&err, dev.pushed_at, "this is `%s`, expected `byte`", dev_str)
		return err
	}

	switch intr.kind {
	case .Add, .Sub, .Mul, .Div:
		expect_n_values(stack, 2, intr.span) or_return

		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		// Wtf ols is doing??
		//  |
		//  v
			// odinfmt: disable
		verb: string
		#partial switch intr.kind {
		case .Add: verb = "add"
		case .Sub: verb = "substruct"
		case .Mul: verb = "multiply"
		case .Div: verb = "divide"
		case: unreachable()
		}
		// odinfmt: enable

		// Types mismatch.
		if !type_eq_downcasted(a.type, b.type) {
			MSG :: "can't %s different types, got `%s` and `%s` on the %s stack"

			a_str := type_tprint(a.type)
			b_str := type_tprint(b.type)
			err := problemf(intr.span, MSG, verb, a_str, b_str, sname)
			problem_notef(&err, a.pushed_at, "this is `%s`", a_str)
			problem_notef(&err, b.pushed_at, "this is `%s`", b_str)
			return err
		}

		stack_push(stack, a.type, intr.span)

	case .Inc:
		expect_n_values(stack, 1, intr.span) or_return
		a := stack_pop(stack)
		is_short = type_is_short(a.type)
		stack_push(stack, a.type, intr.span)

	case .Shift:
		if count < 2 {
			MSG :: "expected an operand and a shift amount on the %s stack, but got %s"
			return problemf(intr.span, MSG, sname, msg_n_values(count))
		}

		amount := stack_pop(stack)
		operand := stack_pop(stack)
		is_short = type_is_short(operand.type)

		_, is_byte := amount.type.(Type_Byte)
		if !is_byte {
			MSG :: "shift amount must be a `byte`, but got a `%s` on the %s stack"

			amount_str := type_tprint(amount.type)
			err := problemf(intr.span, MSG, amount_str, sname)
			problem_notef(&err, amount.pushed_at, "this is `%s`, expected `byte`", amount_str)
			return err
		}

		if !type_is_basic(operand.type) {
			MSG :: "shift operand must be either a `byte` or a `short`, but got a `%s` on the %s stack"
			NOTE :: "this is `%s`, expected `byte` or `short`"

			op_str := type_tprint(operand.type)
			err := problemf(intr.span, MSG, op_str, sname)
			problem_notef(&err, operand.pushed_at, NOTE, op_str)
			return err
		}

		stack_push(stack, operand.type, intr.span)

	case .And, .Or, .Xor:
		expect_n_values(stack, 2, intr.span) or_return

		b := stack_pop(stack)
		a := stack_pop(stack)
		a_str := type_tprint(a.type)
		b_str := type_tprint(b.type)
		is_short = type_is_short(a.type)

		a_basic := type_is_basic(a.type)
		b_basic := type_is_basic(b.type)
		if !a_basic || !b_basic {
			MSG :: "logic operations are only allowed on `byte` or `short` types, but got `%s` and `%s` on the %s stack"
			NOTE :: "this is `%s`, expected `byte` or `short`"

			err := problemf(intr.span, MSG, a_str, b_str, sname)
			if !a_basic do problem_notef(&err, a.pushed_at, NOTE, a_str)
			if !b_basic do problem_notef(&err, b.pushed_at, NOTE, b_str)
			return err
		}

		if !type_eq_downcasted(a.type, b.type) {
			MSG :: "can't do logic operation on different types, got `%s` and `%s` on the %s stack"

			err := problemf(intr.span, MSG, a_str, b_str, sname)
			problem_notef(&err, a.pushed_at, "this is `%s`", a_str)
			problem_notef(&err, b.pushed_at, "this is `%s`", b_str)
			return err
		}

		stack_push(stack, a.type, intr.span)

	case .Eq, .Neq, .Gth, .Lth:
		expect_n_values(stack, 2, intr.span) or_return

		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		if !type_similar_downcasted(a.type, b.type) {
			// TODO: write what "similiar" types are.
			MSG :: "can't compare not similar types, got `%s` and `%s` on the %s stack"

			a_str := type_tprint(a.type)
			b_str := type_tprint(b.type)
			err := problemf(intr.span, MSG, a_str, b_str, sname)
			problem_notef(&err, a.pushed_at, "this is `%s`", a_str)
			problem_notef(&err, b.pushed_at, "this is `%s`", b_str)
			return err
		}

		stack_push(stack, Type_Byte{}, intr.span)

	case .Pop:
		if .Keep not_in intr.modes {
			if count < 1 {
				return problemf(intr.span, "%s stack is already empty", sname)
			}

			a := stack_pop(stack)
			is_short = type_is_short(a.type)
		}
	case .Swap:
		expect_n_values(stack, 2, intr.span) or_return
		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		a_size := type_size(a.type)
		b_size := type_size(b.type)
		if a_size != b_size {
			MSG :: "can't swap types of different sizes, got %d and %d bytes on the %s stack"
			err := problemf(intr.span, MSG, a_size, b_size, sname)
			problem_notef(&err, a.pushed_at, "size is %d", a_size)
			problem_notef(&err, b.pushed_at, "size is %d", b_size)
			return err
		}

		stack_push_item(stack, b)
		stack_push_item(stack, a)
	case .Nip:
		expect_n_values(stack, 2, intr.span) or_return
		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		a_size := type_size(a.type)
		b_size := type_size(b.type)
		if a_size != b_size {
			MSG :: "can't nip types of different sizes, got %d and %d bytes on the %s stack"
			err := problemf(intr.span, MSG, a_size, b_size, sname)
			problem_notef(&err, a.pushed_at, "size is %d", a_size)
			problem_notef(&err, b.pushed_at, "size is %d", b_size)
			return err
		}

		stack_push_item(stack, b)
	case .Rot:
		expect_n_values(stack, 3, intr.span) or_return
		c := stack_pop(stack)
		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		a_size := type_size(a.type)
		b_size := type_size(b.type)
		c_size := type_size(b.type)
		if a_size != b_size || b_size != c_size {
			MSG :: "can't rotate types of different sizes, got %d, %d and %d bytes on the %s stack"
			err := problemf(intr.span, MSG, a_size, b_size, c_size, sname)
			problem_notef(&err, a.pushed_at, "size is %d", a_size)
			problem_notef(&err, b.pushed_at, "size is %d", b_size)
			problem_notef(&err, b.pushed_at, "size is %d", c_size)
			return err
		}

		stack_push_item(stack, b)
		stack_push_item(stack, c)
		stack_push_item(stack, a)
	case .Dup:
		if count < 1 {
			return problemf(intr.span, "no values to duplicate on the %s stack", sname)
		}

		a := stack_pop(stack)
		is_short = type_is_short(a.type)
		stack_push_item(stack, a)
		stack_push(stack, a.type, intr.span, a.name)
	case .Over:
		expect_n_values(stack, 2, intr.span) or_return
		b := stack_pop(stack)
		a := stack_pop(stack)
		is_short = type_is_short(a.type)

		a_size := type_size(a.type)
		b_size := type_size(b.type)
		if a_size != b_size {
			MSG :: "can't over types of different sizes, got %d and %d bytes on the %s stack"
			err := problemf(intr.span, MSG, a_size, b_size, sname)
			problem_notef(&err, a.pushed_at, "size is %d", a_size)
			problem_notef(&err, b.pushed_at, "size is %d", b_size)
			return err
		}

		stack_push_item(stack, a)
		stack_push_item(stack, b)
		stack_push_item(stack, a)
	case .Sth:
		if count < 1 {
			return problemf(intr.span, "no values to stash on the %s stack", sname)
		}
		a := stack_pop(stack)
		is_short = type_is_short(a.type)
		stack_push_item(secondary, a)

	case .Load:
		if count < 1 {
			MSG :: "expected a pointer on the %s stack, but got nothing"
			return problemf(intr.span, MSG, sname)
		}

		ptr := stack_pop(stack)
		ptr_base: ^Complex_Type

		#partial switch ty in ptr.type {
		case Type_Byte_Ptr:
			ptr_base = ty.base
		case Type_Short_Ptr:
			ptr_base = ty.base
		case Type_Func_Ptr:
			MSG :: "can't load function pointers, got `%s` on the %s stack"

			ptr_str := type_tprint(ptr.type)
			err := problemf(intr.span, MSG, ptr_str, sname)
			problem_notef(&err, ptr.pushed_at, "this is `%s`", ptr_str)
			return err
		case:
			// TODO: show what pointers are.
			MSG :: "got a `%s` on the %s stack which is not a pointer, therefore it can't be loaded"

			ptr_str := type_tprint(ptr.type)
			err := problemf(intr.span, MSG, ptr_str, sname)
			problem_notef(&err, ptr.pushed_at, "this is `%s`, expected pointer", ptr_str)
			return err
		}

		type, err := to_stack_type(ptr_base^, intr.span)
		if problem, ok := err.?; ok {
			clear(&problem.notes)
			NOTE :: "while loading pointer `%s`"
			problem_notef(&problem, ptr.pushed_at, NOTE, type_tprint(ptr.type))
			return err
		}

		is_short = type_is_short(type)
		stack_push(stack, type, intr.span)
	case .Store:
		if count < 2 {
			MSG :: "expected a value and a pointer on the %s stack, but got %s"
			return problemf(intr.span, MSG, sname, msg_n_values(count))
		}

		ptr := stack_pop(stack)
		value := stack_pop(stack)
		ptr_base_complex: ^Complex_Type
		is_short = type_is_short(value.type)

		#partial switch ty in ptr.type {
		case Type_Byte_Ptr:
			ptr_base_complex = ty.base
		case Type_Short_Ptr:
			ptr_base_complex = ty.base
		case Type_Func_Ptr:
			MSG :: "can't store into function pointers, got `%s` on the %s stack"

			ptr_str := type_tprint(ptr.type)
			err := problemf(intr.span, MSG, ptr_str, sname)
			problem_notef(&err, ptr.pushed_at, "this is `%s`", ptr_str)
			return err
		case:
			// TODO: show what pointers are.
			MSG :: "got a `%s` on the %s stack which is not a pointer, therefore you can't store into it"

			ptr_str := type_tprint(ptr.type)
			err := problemf(intr.span, MSG, ptr_str, sname)
			problem_notef(&err, ptr.pushed_at, "this is `%s`, expected pointer", ptr_str)
			return err
		}

		ptr_base := to_store_type(ptr_base_complex^, ptr.pushed_at) or_return

		value_type := type_downcast(value.type)
		if !type_eq(value_type, ptr_base) {
			MSG :: "expected a `%s` on the %s stack, the given `%s` can't be stored into a `%s`"
			NOTE :: "this is `%s`, expected `%s`"
			NOTE_2 :: "while storing into pointer `%s`"

			value_str := type_tprint(value.type)
			ptr_str := type_tprint(ptr.type)
			base_str := type_tprint(ptr_base)
			err := problemf(intr.span, MSG, base_str, sname, value_str, ptr_str)
			problem_notef(&err, value.pushed_at, NOTE, value_str, base_str)
			problem_notef(&err, ptr.pushed_at, NOTE_2, ptr_str)
			return err
		}

	case .Call:
		panic("TODO: check intr Call")

	case .Input, .Input2:
		if count < 1 {
			MSG :: "expected a device on the %s stack, but got nothing"
			return problemf(intr.span, MSG, sname)
		}

		dev := stack_pop(stack)
		check_dev_type(stack, dev, intr.span) or_return

		if intr.kind == .Input2 {
			stack_push(stack, Type_Short{}, intr.span)
			is_short = true
		} else {
			stack_push(stack, Type_Byte{}, intr.span)
		}
	case .Output:
		if count < 2 {
			MSG :: "expected a value and a device on the %s stack, but got %s"
			return problemf(intr.span, MSG, sname, msg_n_values(count))
		}

		dev := stack_pop(stack)
		value := stack_pop(stack)
		is_short = type_is_short(value.type)

		check_dev_type(stack, dev, intr.span) or_return
	}

	if is_short {
		intr.modes += {.Short}
	}

	return nil
}
