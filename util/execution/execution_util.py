"""Utilities related to function execution."""

import multiprocessing
from collections.abc import Callable
from typing import Any

from loguru import logger

TERMINATION_GRACE_PERIOD_SEC = 5


def _worker(
    queue: multiprocessing.Queue, function: Callable[..., Any], *args: Any, **kwargs: Any
) -> None:
    """Wrap the runs the function and put the result (or exception) on the queue.

    Args:
        queue: (multiprocessing.Queue): The queue for multiprocessing.
        function (Callable): The function to call.
        *args (Any): The arguments with which to call the function.
        **kwargs (Any): The keyword arguments with which to call the function.
    """
    try:
        result = function(*args, **kwargs)
        queue.put(("success", result))
    except Exception as e:
        queue.put(("error", e))


def run_with_timeout(
    function: Callable[..., Any], *args: Any, timeout_sec: float, **kwargs: Any
) -> Any:
    """Run function with the arguments with the given timeout.

    Uses multiprocessing to ensure the function is actually terminated when the timeout expires.

    Args:
        function (Callable): The function to call.
        *args (Any): The arguments with which to call the function.
        timeout_sec (float): The timeout, given in seconds.
        **kwargs (Any): The keyword arguments with which to call the function.

    Raises:
        TimeoutError: If the function does not complete within the timeout.

    Returns:
        The return value of the function.
    """
    func_name = getattr(function, "__name__", repr(function))
    logger.debug(f"Calling '{func_name}' with timeout = {timeout_sec} (sec)")

    queue: multiprocessing.Queue = multiprocessing.Queue()
    process = multiprocessing.Process(target=_worker, args=(queue, function, *args), kwargs=kwargs)
    process.start()
    process.join(timeout=timeout_sec)

    if process.is_alive():
        process.terminate()
        process.join(timeout=TERMINATION_GRACE_PERIOD_SEC)
        if process.is_alive():
            process.kill()  # Force kill, if necessary.
            process.join()
        raise TimeoutError()

    if not queue.empty():
        status, value = queue.get_nowait()
        if status == "success":
            return value
        raise value  # Re-raise the exception from the child process

    msg = f"'{func_name}' completed but produced no result"
    raise RuntimeError(msg)
