package errors

import "errors"

var (
	ErrOpBusy      = errors.New("operation already running")
	ErrOpNotFound  = errors.New("operation not found")
	ErrInvalidArgs = errors.New("invalid arguments")
	ErrInternal    = errors.New("internal error")
)
