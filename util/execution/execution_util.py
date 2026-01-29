"""Utilities related to function execution."""

from collections.abc import Callable
from concurrent import futures
from typing import Any

from loguru import logger


def run_with_timeout(function: Callable[..., Any], *args: Any, timeout_sec: float, **kwargs: Any):
    """Run function with the arguments with the given timeout.

    Args:
        function (Callable): The function to call.
        *args (Any): The arguments with which to call the function.
        timeout_sec (float): The timeout, given in seconds.
        **kwargs (Any): The keyword arguments with which to call the function.
    """
    with futures.ThreadPoolExecutor() as executor:
        future = executor.submit(function, *args, **kwargs)
        try:
            future.result(timeout=timeout_sec)
        except futures.TimeoutError:
            func_name = getattr(function, "__name__", repr(function))
            logger.error(f"Call to '{func_name}' timed out after {timeout_sec} seconds")
