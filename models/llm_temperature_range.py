"""Module to represent legal temperature ranges for LLMs."""

from argparse import ArgumentTypeError


class LlmTemperatureRange:
    """Represent a legal temperature range for text generation.

    Attributes:
        _start_inclusive (float): The start of the range, inclusive.
        _end_inclusive (float): The end of the range, inclusive.
    """

    def __init__(self, start_inclusive: float, end_inclusive: float):
        """Create a new temperature range for text generation."""
        self._start_inclusive = start_inclusive
        self._end_inclusive = end_inclusive

    def validate_temperature(self, temp_str: str) -> float:
        """Return True iff the given temperature is within this range.

        Args:
            temp_str (str): The temperature to validate.

        Returns:
            float: The validated temperature.
        """
        try:
            temp = float(temp_str)
            if temp < self._start_inclusive or temp > self._end_inclusive:
                msg = (
                    "Temperature must be a float in the range: "
                    f"{self._start_inclusive} - {self._end_inclusive} (inclusive)"
                )
                raise ArgumentTypeError(msg)
            return temp
        except ValueError as ve:
            msg = (
                "Temperature must be a float in the range: "
                f"{self._start_inclusive} - {self._end_inclusive} (inclusive)"
            )
            raise ArgumentTypeError(msg) from ve


OPENAI_MODEL_TEMPERATURE_RANGE = LlmTemperatureRange(start_inclusive=0, end_inclusive=2)
