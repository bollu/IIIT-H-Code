class CreateUserSurveyAnswerStatuses < ActiveRecord::Migration[5.0]
  def change
    create_table :user_survey_answer_statuses do |t|

      t.timestamps
    end
  end
end
