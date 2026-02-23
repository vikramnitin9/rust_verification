"""Utilities related to function execution."""

import multiprocessing
from collections.abc import Callable
from typing import Any

from loguru import logger

TERMINATION_GRACE_PERIOD_SEC = 5


def run_with_timeout(function: Callable[..., Any], *args: Any, timeout_sec: float, **kwargs: Any):
    """Run function with the arguments with the given timeout.

    Uses multiprocessing to ensure the function is actually terminated when the timeout expires.

    Args:
        function (Callable): The function to call.
        *args (Any): The arguments with which to call the function.
        timeout_sec (float): The timeout, given in seconds.
        **kwargs (Any): The keyword arguments with which to call the function.

    Raises:
        TimeoutError: If the function does not complete within the timeout.
    """
    func_name = getattr(function, "__name__", repr(function))
    logger.debug(f"Calling '{func_name}' with timeout = {timeout_sec} (sec)")

    process = multiprocessing.Process(target=function, args=args, kwargs=kwargs)
    process.start()
    process.join(timeout=timeout_sec)

    if process.is_alive():
        process.terminate()
        process.join(timeout=TERMINATION_GRACE_PERIOD_SEC)
        if process.is_alive():
            process.kill()  # Force kill, if necessary.
            process.join()
        raise TimeoutError()

    if process.exitcode != 0:
        raise RuntimeError(
            f"'{func_name}' failed with exit code {process.exitcode}"
        )
