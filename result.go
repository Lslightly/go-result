package result

// Result[T] = OkT[T] + ErrorT[T]
type Result[T any] interface {
	Unwrap() T
	UnwrapUnchecked() T
	UnwrapErr() error
	UnwrapErrUnchecked() error
	UnwrapOr(value T) T
	UnwrapOrDefault() T
	UnwrapOrElse(op func(err error) T) T
	Expect(msg string) T
	ExpectFatal(msg string, fatal func(v ...any)) T
	ExpectErr(msg string) error
	ExpectErrFatal(msg string, fatal func(v ...any)) error
	Inspect(f func(value T)) Result[T]
	InspectErr(f func(err error)) Result[T]
	Err() Option[error]
	Ok() Option[T]
	Or(value Result[T]) Result[T]
	OrElse(op func(err error) Result[T]) Result[T]
	Cloned() Result[T]
	IsOk() bool
	IsOkAnd(f func(value T) bool) bool
	IsErr() bool
	IsErrAnd(f func(err error) bool) bool
	MapErr(op func(err error) error) Result[T]
}

type OkT[T any] struct {
	value T
}

func Default[T any]() (res T) { return }

func (ok OkT[T]) Unwrap() T                                      { return ok.value }
func (ok OkT[T]) UnwrapUnchecked() T                             { return ok.value }
func (ok OkT[T]) UnwrapErr() error                               { panic("called `called `Result.UnwrapErr()` on an `Ok` value") }
func (ok OkT[T]) UnwrapErrUnchecked() error                      { return nil }
func (ok OkT[T]) UnwrapOr(value T) T                             { return ok.value }
func (ok OkT[T]) UnwrapOrDefault() T                             { return ok.value }
func (ok OkT[T]) UnwrapOrElse(op func(err error) T) T            { return ok.value }
func (ok OkT[T]) Expect(msg string) T                            { return ok.value }
func (ok OkT[T]) ExpectFatal(msg string, fatal func(v ...any)) T { return ok.value }
func (ok OkT[T]) ExpectErr(msg string) error                     { return nil }
func (ok OkT[T]) ExpectErrFatal(msg string, fatal func(v ...any)) error {
	fatal(msg)
	return nil
}
func (ok OkT[T]) Inspect(f func(value T)) Result[T] {
	f(ok.value)
	return ok
}
func (ok OkT[T]) InspectErr(f func(err error)) Result[T]        { return ok }
func (ok OkT[T]) Err() Option[error]                            { return None[error]() }
func (ok OkT[T]) Ok() Option[T]                                 { return Some(ok.value) }
func (ok OkT[T]) Or(value Result[T]) Result[T]                  { return ok }
func (ok OkT[T]) OrElse(op func(err error) Result[T]) Result[T] { return ok }
func (ok OkT[T]) Cloned() Result[T]                             { return ok }
func (ok OkT[T]) IsOk() bool                                    { return true }
func (ok OkT[T]) IsOkAnd(f func(value T) bool) bool             { return f(ok.value) }
func (ok OkT[T]) IsErr() bool                                   { return false }
func (ok OkT[T]) IsErrAnd(f func(err error) bool) bool          { return false }
func (ok OkT[T]) MapErr(op func(err error) error) Result[T]     { return ok }

func (e ErrorT[T]) Unwrap() (res T)                     { panic(e.err) }
func (e ErrorT[T]) UnwrapUnchecked() (res T)            { return }
func (e ErrorT[T]) UnwrapErr() error                    { return e.err }
func (e ErrorT[T]) UnwrapErrUnchecked() error           { return e.err }
func (e ErrorT[T]) UnwrapOr(value T) T                  { return value }
func (e ErrorT[T]) UnwrapOrDefault() (res T)            { return }
func (e ErrorT[T]) UnwrapOrElse(op func(err error) T) T { return op(e.err) }
func (e ErrorT[T]) Expect(msg string) T                 { panic(msg) }
func (e ErrorT[T]) ExpectFatal(msg string, fatal func(v ...any)) (res T) {
	fatal(msg)
	return
}
func (e ErrorT[T]) ExpectErr(msg string) error                            { return e.err }
func (e ErrorT[T]) ExpectErrFatal(msg string, fatal func(v ...any)) error { return e.err }
func (e ErrorT[T]) Inspect(f func(value T)) Result[T]                     { return e }
func (e ErrorT[T]) InspectErr(f func(err error)) Result[T] {
	f(e.err)
	return e
}
func (e ErrorT[T]) Err() Option[error]                            { return Some(e.err) }
func (e ErrorT[T]) Ok() Option[T]                                 { return None[T]() }
func (e ErrorT[T]) Or(value Result[T]) Result[T]                  { return value }
func (e ErrorT[T]) OrElse(op func(err error) Result[T]) Result[T] { return op(e.err) }
func (e ErrorT[T]) Cloned() Result[T]                             { return e }
func (e ErrorT[T]) IsOk() bool                                    { return false }
func (e ErrorT[T]) IsOkAnd(f func(value T) bool) bool             { return false }
func (e ErrorT[T]) IsErr() bool                                   { return true }
func (e ErrorT[T]) IsErrAnd(f func(err error) bool) bool          { return f(e.err) }
func (e ErrorT[T]) MapErr(op func(err error) error) Result[T]     { return Err[T](op(e.err)) }

type ErrorT[T any] struct {
	err error
}

func Ok[T any](value T) Result[T] {
	return OkT[T]{
		value: value,
	}
}

func Err[T any](err error) Result[T] {
	return ErrorT[T]{
		err: err,
	}
}

func AsResult[T any](value T, err error) Result[T] {
	if err != nil {
		return Err[T](err)
	}
	return Ok(value)
}
