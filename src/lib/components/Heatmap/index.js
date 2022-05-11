import React, { useState } from "react";
import { addDays, differenceInDays, format, getDay, isSameDay } from "date-fns";
import localeEN from "date-fns/esm/locale/en-US";
import localeES from "date-fns/esm/locale/es";
import localePT from "date-fns/esm/locale/pt-BR";
import localeFR from "date-fns/esm/locale/fr";

import Container from "./components/Container";
import Wrapper from "./components/Wrapper";
import WeekContainer from "./components/WeekContainer";
import WeekLabel from "./components/WeekLabel";
import ColumnsContainer from "./components/ColumnsContainer";
import Column from "./components/Column";
import BoxContainer from "./components/BoxContainer";
import Box from "./components/Box";

const Heatmap = ({
  startDate,
  values,
  showWeekDays,
  showBlockTooltip,
  showLegendTooltip,
  showMonths,
  locale,
  rangeDays,
  boxShape,
  legend,
  contentBeforeLegend,
  contentAfterLegend,
}) => {
  const getLocale = () => {
    if (locale === "pt-br") return localePT;
    else if (locale === "es") return localeES;
    else if (locale === "fr") return localeFR;

    return localeEN;
  };

  const getValue = (refDate) => values?.find((x) => isSameDay(x.date, refDate));

  const getStartDay = () => getDay(startDate);

  const getDaysList = (daysCount) => {
    const daysList = Array(daysCount)
      .fill(0)
      .map((_, index) => {
        const newDate = addDays(startDate, index);
        const customValue = getValue(newDate);

        const { value, valueLabel, onClick } = customValue || {};

        return {
          date: new Date(newDate.setHours(0, 0, 0, 0)),
          value,
          valueLabel: valueLabel ? valueLabel : value,
          onClick,
        };
      });

    return daysList;
  };

  const fillColumn = (daysList, parameters, startDay, index) => {
    const days = daysList
      .filter((x) => x.date >= parameters.refDate)
      .slice(0, index === 0 ? 7 - startDay : 7)
      .filter((x) => x != null);

    const month = days.every(
      (x) => format(x.date, "M") === format(days[0].date, "M")
    )
      ? format(days[0].date, "MMM", {
          locale: finalLocale,
        })
      : "";

    const year = format(parameters.refDate, "y");
    parameters.refDate = addDays(days[days.length - 1]?.date, 1).setHours(
      0,
      0,
      0,
      0
    );

    return {
      index,
      month,
      year,
      days,
    };
  };

  const getColumnsList = (columnsCount, daysList, parameters, startDay) => {
    const columnsList = Array(columnsCount)
      .fill(0)
      .map((_, index) => {
        return fillColumn(daysList, parameters, startDay, index);
      });

    return columnsList;
  };

  const finalLocale = getLocale();

  const getColumns = () => {
    const endDate = addDays(startDate, rangeDays);

    const startDay = getStartDay();
    const isIrregularRange = startDay > 0;

    const daysCount = differenceInDays(endDate, startDate);
    const columnsCount = Math.floor(daysCount / 7) + (isIrregularRange ? 1 : 0);

    const daysList = getDaysList(daysCount);

    const parameters = { refDate: startDate.setHours(0, 0, 0, 0) };

    let columnsList = getColumnsList(
      columnsCount,
      daysList,
      parameters,
      startDay
    );

    const sumDays = columnsList?.reduce((acc, value) => {
      return acc + value.days?.length;
    }, 0);

    if (columnsList && sumDays < daysCount) {
      const newIndex = columnsList[columnsList.length - 1]?.index + 1;
      columnsList = [
        ...columnsList,
        fillColumn(daysList, parameters, startDay, newIndex),
      ];
    }

    return columnsList;
  };

  const [columns] = useState(getColumns());

  const showMonth = (index, month, year) =>
    columns.find((x) => x.month === month && x.year === year)?.index === index;

  return (
    <>
      <Container>
        <Wrapper>
          <WeekContainer>
            {Array(7)
              .fill(0)
              .map((_, index) => (
                <WeekLabel
                  key={`rbh-week-label-${index}`}
                  style={{
                    visibility: showWeekDays.includes(index)
                      ? "visible"
                      : "hidden",
                  }}
                >
                  {finalLocale.localize.day(index, { width: "short" })}
                </WeekLabel>
              ))}
          </WeekContainer>
          <ColumnsContainer>
            {columns &&
              columns.map((column, indexColumn) => {
                const { index, month, year, days } = column;
                return (
                  <Column key={`rbh-column-${index}`}>
                    <span
                      style={{
                        left: index * 14,
                        visibility:
                          showMonths && showMonth(index, month, year)
                            ? "visible"
                            : "hidden",
                      }}
                    >
                      {month}
                    </span>
                    <BoxContainer>
                      {days &&
                        days.map((day, indexDay) => {
                          const startDay = getStartDay();
                          const formulaMargin = startDay * 14;
                          const margin =
                            startDay > 0 ? formulaMargin + 2 : formulaMargin;

                          const boxId = `rbh-box-${indexColumn}-${indexDay}`;

                          return (
                            <Box
                              id={boxId}
                              key={boxId}
                              box={day || {}}
                              showTooltip={showBlockTooltip}
                              boxShape={boxShape}
                              legend={legend}
                              locale={finalLocale}
                              marginTop={
                                index === 0 && indexDay === 0 ? margin || 2 : 2
                              }
                            />
                          );
                        })}
                    </BoxContainer>
                  </Column>
                );
              })}
          </ColumnsContainer>
        </Wrapper>
        <Wrapper legend>
          {contentBeforeLegend && (
            <span style={{ marginRight: 5 }}>{contentBeforeLegend}</span>
          )}
          {legend &&
            legend.map((legend, index) => {
              const boxId = `rbh-legend-box-${index}`;
              return (
                <Box
                  id={boxId}
                  key={boxId}
                  box={{ ...legend, value: legend.label }}
                  showTooltip={showLegendTooltip}
                  boxShape={boxShape}
                />
              );
            })}
          {contentAfterLegend && (
            <span style={{ marginLeft: 5 }}>{contentAfterLegend}</span>
          )}
        </Wrapper>
      </Container>
    </>
  );
};

export default Heatmap;
